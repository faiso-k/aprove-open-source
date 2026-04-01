/**
 *
 * @author mpluecker
 * @version $Id$
 */
package aprove.verification.idpframework.Processors.Poly;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class BigIntSMTEngine implements IDPSMTEngine<BigInt> {

    public static final BigInteger TWO = BigInteger.valueOf(2);

    protected final ISMTChecker smtEngine;

    public BigIntSMTEngine() {
        this.smtEngine = new YicesChecker();
    }

    // ###############################################################################
    // # Non-Linear part
    // ###############################################################################
    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Processors.NonInf.ItpfImplication.IDPSMTEngine#getVarSignum(aprove.verification.idpframework.Core.Itpf.ItpfConjClause, aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation, aprove.strategies.Abortions.Abortion)
     */

    @Override
    public boolean isUnsolvable(final ItpfConjClause precondition,
        final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) throws AbortionException {
        final Map<IVariable<BigInt>, Signum> varSignums = this.getVarSignum(precondition, interpretation, true, aborter);


        return varSignums.values().contains(Signum.Contradiction);
    }

    @Override
    public Map<IVariable<BigInt>, Signum> getVarSignum(final ItpfConjClause precondition, final PolyInterpretation<BigInt> interpretation, final Abortion aborter) throws AbortionException {
        return this.getVarSignum(precondition, interpretation, false, aborter);
    }

    public Map<IVariable<BigInt>, Signum> getVarSignum(final ItpfConjClause precondition, final PolyInterpretation<BigInt> interpretation, final boolean checkContradiction, final Abortion aborter) throws AbortionException {
        final Pair<CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>>, Map<ItpfPolyAtom<BigInt>, Integer>> smtInit =
            this.initSmtData(precondition, interpretation, aborter);;

        final CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>> varToPolynomials = smtInit.x;

        final Map<ItpfPolyAtom<BigInt>, Integer> unsolvedPolyVariables = smtInit.y;

        final Map<IVariable<BigInt>, Signum> result = new LinkedHashMap<IVariable<BigInt>, Signum>();
            //getLinearVarSignum(precondition, interpretation, aborter);

        final Set<UserDefinedDomain> natDomains = this.getNatDomains(interpretation, precondition, varToPolynomials.keySet());
        for (final IVariable<BigInt> var : varToPolynomials.keySet()) {
            if (natDomains.contains(var)) {
                result.put(var, Signum.Pos);
            }
        }

        for (final IVariable<BigInt> solvedVar : result.keySet()) {
            this.decUnsolvedVariables(varToPolynomials.get(solvedVar), unsolvedPolyVariables);
        }

        while(! unsolvedPolyVariables.isEmpty()) {
            final Pair<IVariable<BigInt>, Signum> solved = this.solveNextVariable(unsolvedPolyVariables, varToPolynomials, result, interpretation, aborter);

            if (solved != null) {
                final Signum oldSignum = result.get(solved.x);

                Signum newSignum;
                if (oldSignum == null) {
                    newSignum = solved.y;
                    this.decUnsolvedVariables(varToPolynomials.get(solved.x), unsolvedPolyVariables);
                } else {
                    newSignum = oldSignum.intersect(solved.y);
                }

                result.put(solved.x, newSignum);

            } else {
                break;
            }
        }

        if (checkContradiction) {
            this.checkContradiction(unsolvedPolyVariables, varToPolynomials, result, interpretation, aborter);
        }

        return result;
    }

    private Set<UserDefinedDomain> getNatDomains(final PolyInterpretation<BigInt> interpretation, final ItpfConjClause precondition, final Set<IVariable<BigInt>> variables) {
        final LinkedHashSet<UserDefinedDomain> natDomains = new LinkedHashSet<UserDefinedDomain>();
        for (final IVariable<BigInt> var : variables) {
            IVariable<?> origVar = interpretation.getReverseVariableInterpretations().get(var);
            if (origVar == null) {
                origVar = var;
            }
            if (origVar.getDomain().isUserDefinedDomain()) {
                final UserDefinedDomain domain = (UserDefinedDomain)origVar.getDomain();
                final Polynomial<BigInt> natConstraint = interpretation.getBooleanPolyVar(ConstantType.NatDomain, domain, null);
                final Boolean condNat = precondition.getLiterals().get(natConstraint);
                if (condNat != null && condNat) {
                    natDomains.add(domain);
                }
            }
        }

        return natDomains;
    }

    private void checkContradiction(final Map<ItpfPolyAtom<BigInt>, Integer> unsolvedPolyVariables,
        final CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>> varToPolynomials,
        final Map<IVariable<BigInt>, Signum> currentSolution,
        final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) {

        for (final Map.Entry<ItpfPolyAtom<BigInt>, Integer> unsolvedPoly : unsolvedPolyVariables.entrySet()) {
            if (unsolvedPoly.getValue() == 0) {
                final boolean contradiction = this.hasContradiction(unsolvedPoly.getKey(), currentSolution, interpretation, aborter);

                if (contradiction) {
                    final ImmutableSet<IVariable<BigInt>> contradictionVars =
                        unsolvedPoly.getKey().getPoly().getVariables();

                    for (final Map.Entry<IVariable<BigInt>, Signum> varSignum : currentSolution.entrySet()) {
                        if (contradictionVars.contains(varSignum.getKey())) {
                            varSignum.setValue(Signum.Contradiction);
                        }
                    }
                }
            }
        }
    }

    private boolean hasContradiction(final ItpfPolyAtom<BigInt> polyAtom,
        final Map<IVariable<BigInt>, Signum> currentSolution,
        final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) {
        Signum totalSignum = Signum.Zero;

        for (final Map.Entry<Monomial<BigInt>, BigInt> monomialCoeff : polyAtom.getPoly().getMonomials().entrySet()) {
            Signum monomialSignum = this.getCoeffSignum(monomialCoeff.getValue());

            for (final Map.Entry<? extends PolyVariable<BigInt>, BigInt> varExponent : monomialCoeff.getKey().getExponents().entrySet()) {
                if (varExponent.getValue().isEven()) {
                    monomialSignum = monomialSignum.multEvenExponent(currentSolution.get(varExponent.getKey()));
                } else {
                    monomialSignum = monomialSignum.mult(currentSolution.get(varExponent.getKey()));
                }
            }

            totalSignum = totalSignum.union(monomialSignum);

            if (totalSignum.getId() == null) {
                break;
            }
        }

        switch (polyAtom.getConstraintType()) {
        case EQ :
            return totalSignum.isStrict();
        case GE : return totalSignum == Signum.StrictNeg;
        case GT : return totalSignum.isNeg();
        default : throw new UnsupportedOperationException("unknown constraint type");
        }
    }

    private void decUnsolvedVariables(final Collection<ItpfPolyAtom<BigInt>> atomsToDec,
        final Map<ItpfPolyAtom<BigInt>, Integer> unsolvedPolyVariables) {
        for (final ItpfPolyAtom<BigInt> atom : atomsToDec) {
            final Integer current = unsolvedPolyVariables.get(atom);
            if (current != null) {
                unsolvedPolyVariables.put(atom, current - 1);
            }
        }
    }

    private Pair<IVariable<BigInt>, Signum> solveNextVariable(final Map<ItpfPolyAtom<BigInt>, Integer> unsolvedPolyVariables,
        final CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>> varToPolynomials,
        final Map<IVariable<BigInt>, Signum> currentSolution, final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) {

        final Iterator<Map.Entry<ItpfPolyAtom<BigInt>, Integer>> unsolvedPolyIterator = unsolvedPolyVariables.entrySet().iterator();
        while (unsolvedPolyIterator.hasNext()) {
            final Map.Entry<ItpfPolyAtom<BigInt>, Integer> unsolvedPoly = unsolvedPolyIterator.next();

            final boolean singleVariable = unsolvedPoly.getKey().getPoly().getVariables().size() == 1;

            if (unsolvedPoly.getValue() == 1 || unsolvedPoly.getValue() == 0 && singleVariable) {
                final Pair<IVariable<BigInt>, Signum> solved = this.solvePoly(unsolvedPoly.getKey(), singleVariable, varToPolynomials, currentSolution, interpretation, aborter);

                if (solved != null) {
                    unsolvedPolyIterator.remove();
                    return solved;
                }
            }
        }
        return null;
    }

    private Pair<IVariable<BigInt>, Signum> solvePoly(final ItpfPolyAtom<BigInt> itpfPolyAtom, final boolean singleVariable, final CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>> varToPolynomials, final Map<IVariable<BigInt>, Signum> currentSolution, final PolyInterpretation<BigInt> interpretation, final Abortion aborter) {
        IVariable<BigInt> unsolvedVar = null;
        Signum unsolvedVarMonomialSignum = Signum.Zero;

        Signum otherMonomialsSignum = Signum.Zero;

        for (final Map.Entry<Monomial<BigInt>, BigInt> monomial : itpfPolyAtom.getPoly().getMonomials().entrySet()) {
            Signum monomialSignum = this.getCoeffSignum(monomial.getValue());

            boolean containsUnsolvedVar = false;
            for (final Map.Entry<? extends PolyVariable<BigInt>, BigInt> varExponent : monomial.getKey().getExponents().entrySet()) {
                final IVariable<BigInt> polyVar = (IVariable<BigInt>) varExponent.getKey();
                Signum varSignum = null;
                if (!singleVariable) {
                    varSignum = currentSolution.get(polyVar);
                }

                if (varSignum == null) {
                    if (Globals.useAssertions) {
                        assert unsolvedVar == null || unsolvedVar.equals(polyVar) : "two unsolved variables are not allowed";
                    }

                    unsolvedVar = polyVar;
                    if (!varExponent.getValue().isEven()) {
                        containsUnsolvedVar = true;
                    }
                    varSignum = Signum.StrictPos;
                }

                if (varExponent.getValue().isEven()) {
                    monomialSignum = monomialSignum.mult(varSignum.isStrict() ? Signum.StrictPos : Signum.Pos);
                } else {
                    monomialSignum = monomialSignum.mult(varSignum);
                }
            }

            if (containsUnsolvedVar) {
                unsolvedVarMonomialSignum = unsolvedVarMonomialSignum.union(monomialSignum);
                if (unsolvedVarMonomialSignum == Signum.Wild) {
                    return null;
                }
            } else {
                otherMonomialsSignum = otherMonomialsSignum.union(monomialSignum);
                if (otherMonomialsSignum == Signum.Wild) {
                    return null;
                }
            }

        }

        return this.getPolySolution(unsolvedVar, unsolvedVarMonomialSignum, otherMonomialsSignum, itpfPolyAtom.getConstraintType());
    }

    private Pair<IVariable<BigInt>, Signum> getPolySolution(final IVariable<BigInt> unsolvedVar,
        final Signum unsolvedVarMonomialSignum,
        final Signum otherMonomialsSignum, final ConstraintType constraintType) {
        if (unsolvedVar == null) {
            return null;
        }

        if (!otherMonomialsSignum.isNeg() && otherMonomialsSignum != Signum.Zero && constraintType != ConstraintType.EQ) {
            return null;
        }

        if (!unsolvedVarMonomialSignum.isStrict()) {
            return null;
        }

        Signum resultSignum = otherMonomialsSignum;

        if (resultSignum == Signum.Zero) {
            resultSignum = Signum.Neg;
        }

        if (!unsolvedVarMonomialSignum.isNeg()) {
            resultSignum = resultSignum.negate();
        }

        if (constraintType == ConstraintType.GT) {
            resultSignum = resultSignum.makeStrict();
        }

        return new Pair<IVariable<BigInt>, Signum>(unsolvedVar, resultSignum);
    }

    private Signum getCoeffSignum(final BigInt coeff) {
        Signum coeffSignum;
        final int sig = coeff.getBigInt().signum();
        if (sig == 0) {
            coeffSignum = Signum.Zero;
        } else if (sig > 0) {
            coeffSignum = Signum.StrictPos;
        } else {
            coeffSignum = Signum.StrictNeg;
        }
        return coeffSignum;
    }

    /**
     * @param precondition
     * @param interpretation
     * @param aborter
     * @return x: variable -> polynomials, y : polynomial -> number of unresolved variables
     * @throws AbortionException
     */
    private Pair<CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>>, Map<ItpfPolyAtom<BigInt>, Integer>> initSmtData(final ItpfConjClause precondition,
        final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) throws AbortionException {
        final CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>> varToPoly =
            new CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>>();

        final Map<ItpfPolyAtom<BigInt>, Integer> unsolvedPolyVariables = new LinkedHashMap<ItpfPolyAtom<BigInt>, Integer>();

        nextLiteral : for (final Map.Entry<? extends ItpfAtom, Boolean> literal : precondition.getLiterals().entrySet()) {
            if (literal.getKey().isPoly() && literal.getValue().booleanValue()) {
                final ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) literal.getKey();
                final Polynomial<BigInt> poly = polyAtom.getPoly();

                final Set<IVariable<BigInt>> unsolvedVariables = new LinkedHashSet<IVariable<BigInt>>();

                for (final Monomial<BigInt> monomial : poly.getMonomials().keySet()) {

                    for (final PolyVariable<BigInt> polyVar : monomial.getExponents().keySet()) {
                        if (!polyVar.isMax()) {
                            final IVariable<BigInt> realVar = (IVariable<BigInt>) polyVar;
                            unsolvedVariables.add(realVar);
                        } else {
                            continue nextLiteral;
                        }
                    }
                }

                for (final IVariable<BigInt> realVar : unsolvedVariables) {
                    varToPoly.add(realVar, polyAtom);
                }
                unsolvedPolyVariables.put(polyAtom, unsolvedVariables.size());
            }
            aborter.checkAbortion();
        }

        return new Pair<CollectionMap<IVariable<BigInt>, ItpfPolyAtom<BigInt>>, Map<ItpfPolyAtom<BigInt>, Integer>>(varToPoly, unsolvedPolyVariables);
    }

    // ###############################################################################
    // # Linear part, using linear SMT solver
    // ###############################################################################
    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Processors.NonInf.ItpfImplication.IDPSMTEngine#getLinearSolvableClauses(aprove.verification.idpframework.Core.Itpf.Itpf, aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation, aprove.strategies.Abortions.Abortion)
     */
    @Override
    public Set<ItpfConjClause> getLinearSolvableClauses(final Itpf precondition,
        final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) throws AbortionException {
        final LinkedHashSet<ItpfConjClause> res = new LinkedHashSet<ItpfConjClause>();
        for (final ItpfConjClause clause : precondition.getClauses()) {
            if (this.isLinearPartSolvable(clause, interpretation, aborter)) {
                res.add(clause);
            }
        }
        return res;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Processors.NonInf.ItpfImplication.IDPSMTEngine#getLinearVarSignum(aprove.verification.idpframework.Core.Itpf.ItpfConjClause, aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation, aprove.strategies.Abortions.Abortion)
     */
    @Override
    public Map<IVariable<BigInt>, Signum> getLinearVarSignum(final ItpfConjClause precondition, final PolyInterpretation<BigInt> interpretation, final Abortion aborter) throws AbortionException {
        if (precondition.getLiterals().isEmpty()) {
            return Collections.emptyMap();
        }
        final FullSharingFactory<BigIntImmutable, GPolyVar> gPolyFactory =
            new FullSharingFactory<BigIntImmutable, GPolyVar>();

        final Pair<List<ImmutableBoolOp<LIAConstraint>>, Map<IVariable<BigInt>, GPolyVar>> linearCs = this.getLinearConstraints(precondition, interpretation, gPolyFactory, aborter);
        final ImmutableBoolOp<LIAConstraint> linearConstraints = ImmutableBoolOp.createConjunction(linearCs.x);
        final Map<IVariable<BigInt>, GPolyVar> varMapping = linearCs.y;

        final YNM solution = this.smtEngine.isSatisfiable(linearConstraints, aborter);
        if (solution == YNM.YES) {
            final Map<IVariable<BigInt>, Signum> varSignum = new LinkedHashMap<IVariable<BigInt>, Signum>();

            for (final Map.Entry<IVariable<BigInt>, GPolyVar> varPair : varMapping.entrySet()) {

                final ImmutableBoolOp<LIAConstraint> gtConstraint = this.createVarConstraint(varPair.getValue(), true, true, gPolyFactory);
                final ImmutableBoolOp<LIAConstraint> ltConstraint = this.createVarConstraint(varPair.getValue(), false, true, gPolyFactory);

                final ImmutableBoolOp<LIAConstraint> nonZeroConstraint = ImmutableBoolOp.createDisjunction(gtConstraint, ltConstraint);
                final YNM nonZeroSolution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(linearConstraints, nonZeroConstraint), aborter);

                if (nonZeroSolution == YNM.NO) {
                    varSignum.put(varPair.getKey(), Signum.Zero);
                } else {
                    final ImmutableBoolOp<LIAConstraint> geConstraint = this.createVarConstraint(varPair.getValue(), true, false, gPolyFactory);
                    final YNM geSolution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(linearConstraints, geConstraint), aborter);

                    if (geSolution == YNM.NO) {
                        varSignum.put(varPair.getKey(), Signum.StrictNeg);
                    } else {
                        final ImmutableBoolOp<LIAConstraint> leConstraint = this.createVarConstraint(varPair.getValue(), false, false, gPolyFactory);
                        final YNM leSolution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(linearConstraints, leConstraint), aborter);

                        if (leSolution == YNM.NO) {
                            varSignum.put(varPair.getKey(), Signum.StrictPos);
                        } else {
                            final YNM gtSolution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(linearConstraints, gtConstraint), aborter);

                            if (gtSolution == YNM.NO) {
                                varSignum.put(varPair.getKey(), Signum.Neg);
                            } else {
                                final YNM ltSolution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(linearConstraints, ltConstraint), aborter);

                                if (ltSolution == YNM.NO) {
                                    varSignum.put(varPair.getKey(), Signum.Pos);
                                }
                            }
                        }
                    }
                }
            }
            this.addDomainSignumInformation(varMapping.keySet(), varSignum);

            return varSignum;
        } else {
            return Collections.emptyMap();
        }
    }

    protected void addDomainSignumInformation(final Set<IVariable<BigInt>> vars,
        final Map<IVariable<BigInt>, Signum> varSignum) {
        for (final IVariable<BigInt> IVariable : vars) {
            final SemiRingDomain<BigInt> varRange = IVariable.getDomain();

            Signum sig = varSignum.get(IVariable);
            if (sig == null) {
                sig = Signum.Unknown;
            }

            if (varRange.getMin() != null && varRange.getMin().signum() >= 0) {
                sig = sig.moreSpecific(Signum.Pos);
            }
            if (varRange.getMax() != null && varRange.getMax().signum() <= 0) {
                sig = sig.moreSpecific(Signum.Neg);
            }

            if (sig != Signum.Unknown) {
                varSignum.put(IVariable, sig);
                continue;
            }
        }
    }

    private ImmutableBoolOp<LIAConstraint> createVarConstraint(final GPolyVar var, final boolean greaterZero, final boolean strict, final GPolyFactory<BigIntImmutable, GPolyVar> gPolyFactory) {
        ArithmeticRelation relation;
        if (greaterZero) {
            if (strict) {
                relation = ArithmeticRelation.GT;
            } else {
                relation = ArithmeticRelation.GE;
            }
        } else {
            if (strict) {
                relation = ArithmeticRelation.LT;
            } else {
                relation = ArithmeticRelation.LE;
            }
        }
        return ImmutableBoolOp.createAtom(new LIAConstraint(gPolyFactory.buildFromVariable(var), gPolyFactory.zero(), relation));

    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Processors.NonInf.ItpfImplication.IDPSMTEngine#isLinearPartSolvable(aprove.verification.idpframework.Core.Itpf.ItpfConjClause, aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation, aprove.strategies.Abortions.Abortion)
     */
    @Override
    public boolean isLinearPartSolvable(final ItpfConjClause precondition,
        final PolyInterpretation<BigInt> interpretation,
        final Abortion aborter) throws AbortionException {
        if (precondition.getLiterals().isEmpty()) {
            return true;
        }
        final FullSharingFactory<BigIntImmutable, GPolyVar> gPolyFactory =
            new FullSharingFactory<BigIntImmutable, GPolyVar>();

        final Pair<List<ImmutableBoolOp<LIAConstraint>>, Map<IVariable<BigInt>, GPolyVar>> constraints = this.getLinearConstraints(precondition, interpretation, gPolyFactory, aborter);

        final YNM solution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(constraints.x), aborter);
        return solution != YNM.NO;
    }

    private Pair<List<ImmutableBoolOp<LIAConstraint>>, Map<IVariable<BigInt>, GPolyVar>> getLinearConstraints(final ItpfConjClause precondition,
        final PolyInterpretation<BigInt> interpretation,
        final FullSharingFactory<BigIntImmutable, GPolyVar> gPolyFactory, final Abortion aborter) {

        final List<ImmutableBoolOp<LIAConstraint>> constraints = new ArrayList<ImmutableBoolOp<LIAConstraint>>(precondition.getLiterals().size());
        final Map<IVariable<BigInt>, GPolyVar> varMapping = new LinkedHashMap<IVariable<BigInt>, GPolyVar>();

        final int nextVarId = 0;

        condFor : for (final Map.Entry<? extends ItpfAtom, Boolean> constraint : precondition.getLiterals().entrySet()) {
            final ItpfAtom atom = constraint.getKey();

            if (atom.isPoly() && constraint.getValue().booleanValue()) {
                final ItpfPolyAtom<BigInt> polyAtom = ((ItpfPolyAtom<BigInt>) atom);

                GPoly<BigIntImmutable, GPolyVar> res = null;

                for (final Map.Entry<Monomial<BigInt>, BigInt> monomialCoeff : polyAtom.getPoly().getMonomials().entrySet()) {
                    final Monomial<BigInt> monomial = monomialCoeff.getKey();


                    GPoly<BigIntImmutable, GPolyVar> monomialPoly;
                    if (monomial.getExponents().isEmpty()) {
                        monomialPoly = gPolyFactory.buildFromCoeff(BigIntImmutable.create(monomialCoeff.getValue().getBigInt()));
                    } else {
                        final Map.Entry<? extends PolyVariable<BigInt>, BigInt> varEntry = monomial.getExponents().entrySet().iterator().next();
                        if (varEntry.getKey().isMax()) {
                            continue condFor;
                        } else if (varEntry.getValue().isOne()) {
                            final IVariable<BigInt> realVariable = (IVariable<BigInt>) varEntry.getKey();

                            GPolyVar gVar = varMapping.get(realVariable);

                            if (gVar == null) {
                                gVar = new GAtomicVar(realVariable.getName() + "_" + nextVarId);
                                varMapping.put(realVariable, gVar);
                            }

                            monomialPoly = gPolyFactory.concat(BigIntImmutable.create(monomialCoeff.getValue().getBigInt()),
                                gPolyFactory.buildVariable(gVar));
                        } else {
                            continue condFor;
                        }
                    }

                    if (res == null) {
                        res = monomialPoly;
                    } else {
                        res = gPolyFactory.plus(res, monomialPoly);
                    }
                }

                if (res != null) {
                    constraints.add(ImmutableBoolOp.createAtom(new LIAConstraint(res, gPolyFactory.zero(), this.getArithmeticRelation(polyAtom.getConstraintType()))));
                }
            }
        }

        return new Pair<List<ImmutableBoolOp<LIAConstraint>>, Map<IVariable<BigInt>,GPolyVar>>(constraints, varMapping);
    }

    private ArithmeticRelation getArithmeticRelation(final ConstraintType constraintType) {
        switch(constraintType) {
        case EQ :
            return ArithmeticRelation.EQ;
        case GE :
            return ArithmeticRelation.GE;
        case GT :
            return ArithmeticRelation.GT;
        }

        throw new IllegalArgumentException("unknown constraint type");
    }

}
