package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.complexity.LowerBounds.Util.Transformations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

public class UnifyPolynomials implements EquationalUnificationRule {

    private static Map<Pair<TRSTerm, TRSTerm>, Optional<Set<Result>>> cache = new LinkedHashMap<>();

    @Override
    public Optional<Set<Result>> apply(TRSTerm sArg, TRSTerm tArg, UnificationProblem unificationProblem) {
        if (PFHelper.isArithExp(sArg) && PFHelper.isArithExp(tArg)) {
            if (sArg.isVariable() && !tArg.getVariables().contains(sArg)) {
                if (!unificationProblem.isAssigned((TRSVariable) sArg)) {
                    return Optional.of(Collections.singleton(new Result(TRSSubstitution.create((TRSVariable) sArg, tArg), new UnificationProblem(sArg, tArg))));
                } else {
                    return Optional.empty();
                }
            } else if (tArg.isVariable() && !sArg.getVariables().contains(tArg)) {
                if (!unificationProblem.isAssigned((TRSVariable) tArg)) {
                    return Optional.of(Collections.singleton(new Result(TRSSubstitution.create((TRSVariable) tArg, sArg), new UnificationProblem(sArg, tArg))));
                } else {
                    return Optional.empty();
                }
            }
            TRSTerm sNorm = sArg.renameVariables(TermNormalization.getRenamingMapForVariables(sArg).getLRMap());
            sNorm = sNorm.replaceAll(TermNormalization.getRenamingMapForConstants(sNorm).getLRMap());
            TRSTerm tNorm = tArg.renameVariables(TermNormalization.getRenamingMapForVariables(tArg).getLRMap());
            tNorm = tNorm.replaceAll(TermNormalization.getRenamingMapForConstants(tNorm).getLRMap());
            TRSTerm s;
            TRSTerm t;
            if (sNorm.toString().compareTo(tNorm.toString()) > 0) {
                s = tArg;
                t = sArg;
            } else {
                s = sArg;
                t = tArg;
            }
            BidirectionalMap<TRSVariable, TRSVariable> renaming = TermNormalization.getRenamingMapForVariables(s, t);
            BidirectionalMap<TRSTerm, TRSTerm> constantRenaming = TermNormalization.getRenamingMapForConstants(s, t);
            s = s.renameVariables(renaming.getLRMap()).replaceAll(constantRenaming.getLRMap());
            t = t.renameVariables(renaming.getLRMap()).replaceAll(constantRenaming.getLRMap());
            Pair<TRSTerm, TRSTerm> key = new Pair<>(s, t);
            if (cache.containsKey(key)) {
                return cache.get(key).map(x -> x.stream().map(y -> y.applyVariableRenaming(renaming.getRLMap()).applyConstantRenaming(constantRenaming.getRLMap())).collect(toSet()));
            }
            TermToPolynomial transformer = new TermToPolynomial(null);
            SimplePolynomial sPoly = transformer.transform(s);
            SimplePolynomial tPoly = transformer.transform(t);
            SimplePolynomial poly = sPoly.minus(tPoly);
            if (poly.isZero()) {
                return Optional.of(Collections.emptySet());
            }
            Set<String> varNames = new LinkedHashSet<>(union(s.getVariables(), t.getVariables()).stream().map(x -> x.getName()).collect(toSet()));
            Map<String, TRSFunctionApplication> constantMap = new LinkedHashMap<>();
            Map<TRSVariable, TRSTerm> theta = new LinkedHashMap<>();
            for (TRSFunctionApplication c: transformer.getConstants()) {
                constantMap.put(c.getName(), c);
                theta.put(TRSTerm.createVariable(c.getName()), c);
            }
            Optional<Set<Result>> toReturn = Optional.empty();
            long minLostVariables = Long.MAX_VALUE;
            VAR_LOOP: for (String x: varNames) {
                SimplePolynomial res = poly.minus(SimplePolynomial.create(x)).negate();
                if (res.getIndefinites().contains(x)) {
                    res = poly.plus(SimplePolynomial.create(x));
                }
                if (!res.getIndefinites().contains(x)) {
                    Map<String, SimplePolynomial> sigma = new LinkedHashMap<>();
                    Map<BigInteger, CollectionMap<Integer, String>> constantCoefficients = new LinkedHashMap<>();
                    Map<BigInteger, CollectionMap<Integer, String>> varCoefficients = new LinkedHashMap<>();
                    for (Entry<IndefinitePart, BigInteger> e: res.getSimpleMonomials().entrySet()) {
                        if (e.getKey().numberOfIndefinites() > 1) {
                            if (e.getValue().compareTo(BigInteger.ZERO) < 0) {
                                // if we have a negative mixed monomial, set all of its variables to 0 to get rid of it
                                for (String str: e.getKey().getIndefinites()) {
                                    // if a negative mixed monomial with constants -- no idea what to do in this case
                                    if (constantMap.containsKey(str)) {
                                        continue VAR_LOOP;
                                    }
                                    sigma.put(str, SimplePolynomial.ZERO);
                                }
                            }
                        } else if (e.getKey().numberOfIndefinites() == 1) {
                            // group the monomials by their coefficients and degrees, but keep variables and constants
                            // separated
                            String str = e.getKey().getTheOnlyIndefinite();
                            BigInteger coefficient = e.getValue();
                            int degree = e.getKey().getDegree();
                            if (constantMap.containsKey(str)) {
                                if (!constantCoefficients.containsKey(coefficient)) {
                                    constantCoefficients.put(coefficient, new CollectionMap<>());
                                }
                                constantCoefficients.get(coefficient).add(degree, str);
                            } else {
                                if (!varCoefficients.containsKey(coefficient)) {
                                    varCoefficients.put(coefficient, new CollectionMap<>());
                                }
                                varCoefficients.get(coefficient).add(degree, str);
                            }
                        }
                    }
                    // those variables which occur with positive coefficients only can be used to eliminate negative
                    // monomials
                    Set<String> posVars = new LinkedHashSet<>();
                    Set<String> nonPosVars = new LinkedHashSet<>();
                    for (Entry<BigInteger, CollectionMap<Integer, String>> e: varCoefficients.entrySet()) {
                        if (e.getKey().compareTo(BigInteger.ZERO) < 0) {
                            for (Collection<String> c: e.getValue().values()) {
                                nonPosVars.addAll(c);
                            }
                        } else {
                            for (Collection<String> c: e.getValue().values()) {
                                posVars.addAll(c);
                            }
                        }
                    }
                    posVars.removeAll(nonPosVars);
                    // if a constant c is subtracted, then we set some monomial with coefficient -c to 1
                    if (res.getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {
                        CollectionMap<Integer, String> others = varCoefficients.get(res.getNumericalAddend().negate());
                        if (others == null) {
                            continue VAR_LOOP;
                        }
                        OUTER: for (Collection<String> c: others.values()) {
                            Iterator<String> cIt = c.iterator();
                            while (cIt.hasNext()) {
                                String other = cIt.next();
                                if (posVars.contains(other)) {
                                    sigma.put(other, SimplePolynomial.ONE);
                                    cIt.remove();
                                    break OUTER;
                                }
                            }
                            // we didn't find a suitable variable -- try to resolve the polynomial for another
                            // variable
                            continue VAR_LOOP;
                        }
                    }
                    // if a constant occurs with a negative coefficient, instantiate some variable with this constant
                    for (BigInteger i: constantCoefficients.keySet()) {
                        if (i.compareTo(BigInteger.ZERO) < 0) {
                            CollectionMap<Integer, String> others = varCoefficients.get(i.negate());
                            if (others == null) {
                                continue VAR_LOOP;
                            }
                            for (Entry<Integer, Collection<String>> e: constantCoefficients.get(i).entrySet()) {
                                int degree = e.getKey();
                                Collection<String> constants = e.getValue();
                                Collection<String> variables = others.get(degree);
                                if (variables == null) {
                                    continue VAR_LOOP;
                                }
                                Iterator<String> varIt = variables.iterator();
                                CONSTANT_LOOP: for (String constant: constants) {
                                    while (varIt.hasNext()) {
                                        String var = varIt.next();
                                        if (posVars.contains(var)) {
                                            sigma.put(var, SimplePolynomial.create(constant));
                                            varIt.remove();
                                            // we found a suitable variable -- instantiate it and continue with
                                            // the next constant
                                            continue CONSTANT_LOOP;
                                        }
                                    }
                                    // we didn't find a suitable variable -- try to resolve the polynomial for
                                    // another variable
                                    continue VAR_LOOP;
                                }
                            }
                        }
                    }
                    // if a variable occurs with a negative coefficient, instantiate some other variable with it
                    for (BigInteger i: varCoefficients.keySet()) {
                        if (i.compareTo(BigInteger.ZERO) < 0 && !varCoefficients.get(i).isEmpty()) {
                            CollectionMap<Integer, String> others = varCoefficients.get(i.negate());
                            if (others == null) {
                                others = new CollectionMap<>();
                            }
                            for (Entry<Integer, Collection<String>> e: varCoefficients.get(i).entrySet()) {
                                int degree = e.getKey();
                                Collection<String> negVars = e.getValue();
                                Collection<String> variables = others.get(degree);
                                if (variables == null) {
                                    variables = new LinkedHashSet<String>();
                                }
                                Iterator<String> varIt = variables.iterator();
                                NEG_VAR_LOOP: for (String negVar: negVars) {
                                    // if we already instantiated this variable with 0, then there's nothing left to do
                                    if (!sigma.containsKey(negVar) || !sigma.get(negVar).isZero()) {
                                        while (varIt.hasNext()) {
                                            String var = varIt.next();
                                            if (posVars.contains(var)) {
                                                sigma.put(negVar, SimplePolynomial.create(var));
                                                varIt.remove();
                                                // we found a suitable variable -- instantiate it and continue with
                                                // the next negative variable
                                                continue NEG_VAR_LOOP;
                                            }
                                        }
                                        // we didn't find a suitable variable -- instantiate this one with 0
                                        sigma.put(negVar, SimplePolynomial.ZERO);
                                    }
                                }
                            }
                        }
                    }
                    res = res.substitute(sigma);
                    assert (res.allPositive());
                    TRSSubstitution thetaSubs = TRSSubstitution.create(ImmutableCreator.create(theta));
                    TRSTerm termRes = res.toOrderedTerm().applySubstitution(thetaSubs);
                    TRSVariable xVar = TRSTerm.createVariable(x);
                    Map<TRSVariable, TRSTerm> refinement = new LinkedHashMap<>();
                    UnificationProblem up = new UnificationProblem();
                    refinement.put(xVar, termRes);
                    up.add(xVar, termRes);
                    for (Entry<String, SimplePolynomial> e: sigma.entrySet()) {
                        TRSVariable var = TRSTerm.createVariable(e.getKey());
                        TRSTerm term = e.getValue().toOrderedTerm().applySubstitution(thetaSubs);
                        refinement.put(var, term);
                        up.add(var, term);
                    }
                    TRSSubstitution refinementSubs = TRSSubstitution.create(ImmutableCreator.create(refinement));
                    TRSSubstitution oldRefinemenSubs;
                    do {
                        oldRefinemenSubs = refinementSubs;
                        refinementSubs = refinementSubs.compose(refinementSubs);
                    } while (!oldRefinemenSubs.equals(refinementSubs));
                    long lostVariables = refinementSubs.getCodomain().stream().filter(PFHelper::isInt).count();
                    if (!toReturn.isPresent()) {
                        toReturn = Optional.of(new LinkedHashSet<>());
                    }
                    if (lostVariables < minLostVariables) {
                        minLostVariables = lostVariables;
                        toReturn.get().clear();
                        toReturn.get().add(new Result(refinementSubs, up));
                    } else if (lostVariables == minLostVariables) {
                        toReturn.get().add(new Result(refinementSubs, up));
                    }
                }
            }
            cache.put(key, toReturn);
            return toReturn.map(x -> x.stream().map(y -> y.applyVariableRenaming(renaming.getRLMap()).applyConstantRenaming(constantRenaming.getRLMap())).collect(toSet()));
        }
        return Optional.empty();
    }

}
