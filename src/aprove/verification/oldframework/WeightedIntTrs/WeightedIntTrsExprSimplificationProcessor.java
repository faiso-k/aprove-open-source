package aprove.verification.oldframework.WeightedIntTrs;

import static java.util.stream.Collectors.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.Collections.*;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;

public class WeightedIntTrsExprSimplificationProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) {
        Map<T, Optional<T>> m = obl.getRules().stream().collect(toMap(x -> x, this::simplify));
        Set<T> newRules = m.values().stream().filter(x -> x.isPresent()).map(x -> x.get()).collect(toSet());
        if (obl.getRules().containsAll(newRules)) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(obl.copyWithNewRules(newRules), BothBounds.forConcreteBounds(), new ExpressionSimplificationProof<>(m));
        }
    }

    private <T extends AbstractWeightedIntRule<T>> Optional<T> simplify(T rule) {
       List<TRSFunctionApplication> newRhs = new ArrayList<>(rule.getRight().size());
       for (TRSFunctionApplication r : rule.getRight()) {
           List<TRSTerm> newArgs = r.getArguments().stream().map(this::simplifyPoly).collect(toList());
           newRhs.add( TRSTerm.createFunctionApplication(r.getRootSymbol(), newArgs));
       }
       try {
           TRSFunctionApplication newCond = simplifyCondition(rule.getCondition());
           return Optional.of(rule.copy(rule.getLeft(), newRhs, newCond, rule.getLeftOutputVariables()));
       } catch (UnsatException e) {
           return Optional.empty();
       }
    }

    private TRSTerm simplifyPoly(TRSTerm t) {
        TRSTerm normalized = termToPoly(t).map(SimplePolynomial::toTerm).orElse(t);
        return recursivelySimplifyPoly(normalized);
    }

    @SuppressWarnings("serial")
    private static class UnsatException extends Exception{}

    private Optional<TRSFunctionApplication> simplifyConstraint(TRSFunctionApplication tFun) throws UnsatException {
        FunctionSymbol root = tFun.getRootSymbol();
        if (root.equals(PFHelper.NOT)) {
            try {
                Optional<TRSFunctionApplication> firstArg = simplifyConstraint((TRSFunctionApplication) tFun.getArgument(0));
                if (firstArg.isPresent()) {
                    return Optional.of(negate(firstArg.get()));
                } else {
                    throw new UnsatException();
                }
            } catch (UnsatException e) {
                return Optional.empty();
            }
        } else if (root.equals(PFHelper.TRUE.getSym())) {
            return Optional.empty();
        }
        TRSTerm firstArg = simplifyPoly(tFun.getArgument(0));
        TRSTerm secondArg = simplifyPoly(tFun.getArgument(1));
        if (PFHelper.isInt(firstArg) && PFHelper.isInt(secondArg)) {
            if (checkRelation(firstArg, root, secondArg)) {
                return Optional.empty();
            } else {
                throw new UnsatException();
            }
        }
        return Optional.of(TRSTerm.createFunctionApplication(root, firstArg, secondArg));
    }

    private TRSFunctionApplication gtToLt(TRSFunctionApplication t) {
        if (t.getRootSymbol().equals(PFHelper.GE)) {
            return TRSTerm.createFunctionApplication(PFHelper.LE, t.getArgument(1), t.getArgument(0));
        } else if (t.getRootSymbol().equals(PFHelper.GT)) {
            return TRSTerm.createFunctionApplication(PFHelper.LT, t.getArgument(1), t.getArgument(0));
        } else {
            return t;
        }
    }

    private Set<TRSFunctionApplication> stricter(TRSFunctionApplication t) {
        Set<TRSFunctionApplication> res = new LinkedHashSet<>();
        if (t.getRootSymbol().equals(PFHelper.LE)) {
            res.add(TRSTerm.createFunctionApplication(PFHelper.LT, t.getArguments()));
            res.add(TRSTerm.createFunctionApplication(PFHelper.EQ, t.getArguments()));
        }
        return res;
    }

    private TRSFunctionApplication simplifyCondition(TRSFunctionApplication t) throws UnsatException {
        List<TRSFunctionApplication> constraints = getConstraints(t);
        List<Optional<TRSFunctionApplication>> optSimplified = new ArrayList<>();
        for (TRSFunctionApplication c: constraints) {
            optSimplified.add(simplifyConstraint(c));
        }
        List<TRSFunctionApplication> simplified = optSimplified
                .stream()
                .filter(x -> x.isPresent())
                .map(x -> x.get())
                .map(this::gtToLt)
                .collect(toList());
        List<TRSFunctionApplication> res = new ArrayList<>();
        int i = 0;
        for (TRSFunctionApplication c: simplified) {
            if (areDisjoint(stricter(c), simplified) && i == simplified.lastIndexOf(c)) {
                res.add(c);
            }
            i++;
        }
        return (TRSFunctionApplication) ToolBox.buildAnd(res);
    }

    private List<TRSFunctionApplication> getConstraints(TRSFunctionApplication t) {
        if (t.getRootSymbol().equals(PFHelper.AND)) {
            List<TRSFunctionApplication> res = new ArrayList<>();
            res.addAll(getConstraints((TRSFunctionApplication) t.getArgument(0)));
            res.addAll(getConstraints((TRSFunctionApplication) t.getArgument(1)));
            return res;
        } else {
            return singletonList(t);
        }
    }

    private boolean checkRelation(TRSTerm firstArg, FunctionSymbol root, TRSTerm secondArg) {
        BigInteger firstVal = PFHelper.toInt(firstArg);
        BigInteger secondVal = PFHelper.toInt(secondArg);
        int comp = firstVal.compareTo(secondVal);
        if (root.equals(PFHelper.GE)) {
            return comp >= 0;
        } else if (root.equals(PFHelper.GT)) {
            return comp > 0;
        } else if (root.equals(PFHelper.LE)) {
            return comp <= 0;
        } else if (root.equals(PFHelper.LT)) {
            return comp < 0;
        } else if (root.equals(PFHelper.EQ)) {
            return comp == 0;
        } else if (root.equals(PFHelper.NEQ)) {
            return comp != 0;
        } else {
            throw new RuntimeException();
        }
    }

    private TRSFunctionApplication negate(TRSFunctionApplication t) {
        FunctionSymbol root = t.getRootSymbol();
        if (root.equals(PFHelper.GE)) {
            return TRSTerm.createFunctionApplication(PFHelper.LT, t.getArguments());
        } else if (root.equals(PFHelper.GT)) {
            return TRSTerm.createFunctionApplication(PFHelper.LE, t.getArguments());
        } else if (root.equals(PFHelper.LE)) {
            return TRSTerm.createFunctionApplication(PFHelper.LT, t.getArgument(1), t.getArgument(0));
        } else if (root.equals(PFHelper.LT)) {
            return TRSTerm.createFunctionApplication(PFHelper.LE, t.getArgument(1), t.getArgument(0));
        } else if (root.equals(PFHelper.EQ)) {
            return TRSTerm.createFunctionApplication(PFHelper.NEQ, t.getArguments());
        } else if (root.equals(PFHelper.NEQ)) {
            return TRSTerm.createFunctionApplication(PFHelper.EQ, t.getArguments());
        } else if (root.equals(PFHelper.NOT)) {
            return (TRSFunctionApplication) t.getArgument(0);
        } else {
            throw new RuntimeException();
        }
    }

    private TRSTerm recursivelySimplifyPoly(TRSTerm t) {
        if (t.isVariable()) {
            return t;
        }
        TRSFunctionApplication tFun = (TRSFunctionApplication) t;
        FunctionSymbol root = tFun.getRootSymbol();
        if (root.equals(PFHelper.ADD)) {
            TRSTerm firstArg = recursivelySimplifyPoly(tFun.getArgument(0));
            TRSTerm secondArg = recursivelySimplifyPoly(tFun.getArgument(1));
            if (PFHelper.isInt(firstArg)) {
                BigInteger value = PFHelper.toInt(firstArg);
                if (value.compareTo(BigInteger.ZERO) < 0) {
                    return TRSTerm.createFunctionApplication(PFHelper.SUB, secondArg, PFHelper.toTerm(value.negate()));
                }
            } else if (PFHelper.isInt(secondArg)) {
                BigInteger value = PFHelper.toInt(secondArg);
                if (value.compareTo(BigInteger.ZERO) < 0) {
                    return TRSTerm.createFunctionApplication(PFHelper.SUB, firstArg, PFHelper.toTerm(value.negate()));
                }
            }
            return TRSTerm.createFunctionApplication(PFHelper.ADD, firstArg, secondArg);
        } else {
            return TRSTerm.createFunctionApplication(root, tFun.getArguments().stream().map(this::recursivelySimplifyPoly).collect(toList()));
        }
    }

    private Optional<SimplePolynomial> termToPoly(TRSTerm t) {
        if (t.isVariable()) {
            return Optional.of(SimplePolynomial.create(t.getName()));
        } else if (t.isConstant()) {
            return Optional.of(SimplePolynomial.create(new BigInteger(t.toString())));
        } else {
            TRSFunctionApplication fun = (TRSFunctionApplication) t;
            FunctionSymbol f = fun.getRootSymbol();
            if (f.equals(Func.UnaryMinus.asFunctionSymbol())) {
                return termToPoly(fun.getArgument(0)).map(SimplePolynomial::negate);
            }
            if (f.equals(Func.Add.asFunctionSymbol()) || f.equals(Func.Mul.asFunctionSymbol()) || f.equals(Func.Sub.asFunctionSymbol())) {
                Optional<SimplePolynomial> arg1 = termToPoly(fun.getArgument(0));
                Optional<SimplePolynomial> arg2 = termToPoly(fun.getArgument(1));
                if (arg2.isPresent() ) {
                    if (f.equals(Func.Add.asFunctionSymbol())) {
                        return arg1.map(p -> p.plus(arg2.get()));
                    } else if (f.equals(Func.Mul.asFunctionSymbol())) {
                        return arg1.map(p -> p.times(arg2.get()));
                    } else if (f.equals(Func.Sub.asFunctionSymbol())) {
                        return arg1.map(p -> p.minus(arg2.get()));
                    }
                }
            }
            return Optional.empty();
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof AbstractWeightedIntTermSystem<?>;
    }

    private static class ExpressionSimplificationProof<T extends AbstractWeightedIntRule<T>> extends DefaultProof {

        Map<T, Optional<T>> map;

        public ExpressionSimplificationProof(Map<T, Optional<T>> map) {
            this.map = map;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Simplified expressions.");
            for (Entry<T, Optional<T>> e: map.entrySet()) {
                if (e.getValue().isPresent()) {
                    if (!e.getKey().equals(e.getValue().get())) {
                        sb.append(o.paragraph());
                        sb.append(e.getKey().export(o));
                        sb.append(o.linebreak());
                        sb.append("was transformed to");
                        sb.append(o.linebreak());
                        sb.append(e.getValue().get().export(o));
                    }
                } else {
                    sb.append(o.paragraph());
                    sb.append(e.getKey().export(o));
                    sb.append(o.linebreak());
                    sb.append("was removed");
                }
            }
            return sb.toString();
        }

    }

}
