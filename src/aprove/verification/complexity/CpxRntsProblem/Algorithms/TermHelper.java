package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Auxiliary helper functions for common operations on terms/polynomials.
 * @author mnaaf
 */
public abstract class TermHelper {

    public interface FunFilterLambda {
        public boolean op(FunctionSymbol fun);
    }

    //counts the occurrences of function symbols in this term for which filter returns true
    public static int countFunFilter(TRSTerm term, FunFilterLambda filter) {
        if (term.isVariable()) return 0;
        TRSFunctionApplication funapp = (TRSFunctionApplication)term;
        int res = 0;
        for (TRSTerm arg : funapp.getArguments()) {
            res += countFunFilter(arg, filter);
        }
        if (filter.op(funapp.getRootSymbol())) {
            res += 1;
        }
        return res;
    }

    //counts the occurrences of fun in the given term
    public static int countFun(FunctionSymbol fun, TRSTerm term) {
        return countFunFilter(term, sym -> fun.equals(sym));
    }

    //counts the nesting depth of function symbols that match the given filter
    public static int countFunNesting(TRSTerm term, FunFilterLambda filter) {
        if (term.isVariable()) return 0;
        TRSFunctionApplication funapp = (TRSFunctionApplication)term;
        int res = 0;
        for (TRSTerm arg : funapp.getArguments()) {
            res = Math.max(res, countFunNesting(arg,filter));
        }
        if (filter.op(funapp.getRootSymbol())) {
            res += 1;
        }
        return res;
    }

    //prepends the arguments in the given order to funapp's arguments, creating a new fun symbol
    public static TRSFunctionApplication prependArguments(TRSFunctionApplication funapp, TRSTerm ... args) {
        FunctionSymbol fun = funapp.getRootSymbol();
        FunctionSymbol newFun = FunctionSymbol.create(fun.getName(), fun.getArity()+args.length);

        ArrayList<TRSTerm> newArgs = new ArrayList<>(newFun.getArity());
        for (TRSTerm arg : args) {
            newArgs.add(arg);
        }
        newArgs.addAll(funapp.getArguments());
        return TRSTerm.createFunctionApplication(newFun, newArgs);
    }

    //returns true iff sym is predefined for arithmetic (+,*,... or an integer value)
    public static boolean isIntArithmeticSymbol(FunctionSymbol sym) {
        if (IDPPredefinedMap.DEFAULT_MAP.isInt(sym, DomainFactory.INTEGERS)) {
            return true;
        }
        PredefinedFunction<? extends Domain> predef = IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(sym);
        return (predef != null && predef.isArithmetic());
    }

    //applies the polynomial bound to the given arguments, or returns a fresh variable to indicate infinity
    public static TRSTerm applyBound(CpxRntsProblem rnts, List<TRSTerm> args, Optional<SimplePolynomial> bound) {
        if (!bound.isPresent()) {
            return rnts.generateFreshVariable("inf", false);
        }
        Map<TRSVariable,TRSTerm> submap = new LinkedHashMap<>();
        for (int i=0; i < args.size(); ++i) {
            TRSVariable var = TRSTerm.createVariable(rnts.getArgumentName(i));
            submap.put(var, args.get(i));
        }
        TRSSubstitution subs = TRSSubstitution.create(ImmutableCreator.create(submap));
        return bound.get().toTerm().applySubstitution(subs);
    }

    //transform the given costterm into a polynomial, or returns a fresh variable to indicate cost infinity
    public static SimplePolynomial termToCost(CpxRntsProblem rnts, TRSTerm costterm) {
        try {
            return CpxIntTermHelper.toSimplePolynomial(costterm);
        } catch (NotRepresentableAsPolynomialException e) {
            return SimplePolynomial.create(rnts.generateFreshVariable("inf", false).getName());
        }
    }

    //converts the given integer term to a polynomial expression in the given set of indefinite variables
    //note that other variables are put into the coefficients
    public static VarPolynomial toVarPolynomial(TRSTerm t, Set<TRSVariable> indefiniteVar) throws NotRepresentableAsPolynomialException {
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable)t;
            if (indefiniteVar.contains(v)) {
                return VarPolynomial.createVariable(v.getName());
            } else {
                return VarPolynomial.createCoefficient(v.getName());
            }
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        BigInteger intValue = CpxIntTermHelper.getIntegerValue(fa);
        if (intValue != null) {
            return VarPolynomial.create(intValue);
        }
        if (fs.equals(CpxIntTermHelper.fAdd)) {
            VarPolynomial left = toVarPolynomial(fa.getArgument(0), indefiniteVar);
            VarPolynomial right = toVarPolynomial(fa.getArgument(1), indefiniteVar);
            return left.plus(right);
        }
        if (fs.equals(CpxIntTermHelper.fMul)) {
            VarPolynomial left = toVarPolynomial(fa.getArgument(0), indefiniteVar);
            VarPolynomial right = toVarPolynomial(fa.getArgument(1), indefiniteVar);
            return left.times(right);
        }
        if (fs.equals(CpxIntTermHelper.fSub)) {
            VarPolynomial left = toVarPolynomial(fa.getArgument(0), indefiniteVar);
            VarPolynomial right = toVarPolynomial(fa.getArgument(1), indefiniteVar);
            return left.minus(right);
        }
        if (fs.equals(CpxIntTermHelper.fUnaryMinus)) {
            return toVarPolynomial(fa.getArgument(0), indefiniteVar).negate();
        }
        throw new NotRepresentableAsPolynomialException();
    }

    //creates the constraint "arg >= val". Make sure that arg and val are integer terms!
    public static Constraint makeGreaterEqualConstraint(TRSTerm arg, TRSTerm val) {
        TRSFunctionApplication funapp = TRSTerm.createFunctionApplication(CpxIntTermHelper.fGe, arg, val);
        try {
            return Constraint.create(funapp);
        } catch (NoConstraintTermException e) {
            throw new RuntimeException(e); //internal error
        }
    }

    //returns 1,0,-1 if a is worse (larger), equal or better (tighter) than b (only heuristically).
    //Here, "better" means a tighter bound, or a bound that can be used more easily in further steps
    public static int compareBoundsHeuristic(Optional<SimplePolynomial> a, Optional<SimplePolynomial> b) {
        //compare optionals
        if (!a.isPresent() && !b.isPresent()) return 0;
        if (!a.isPresent()) return 1;
        if (!b.isPresent()) return -1;

        //compare the number of variables
        SimplePolynomial pa = a.get();
        SimplePolynomial pb = b.get();
        int sizediff = pa.getVariables().size() - pb.getVariables().size();
        if (sizediff > 0) return 1; //prefer less variables
        if (sizediff < 0) return -1;

        //check if one polynomial is greater than the other (e.g. x+2 > x+1 or 2*x > x)
        SimplePolynomial diff = pa.minus(pb);
        if (diff.allNegative()) return -1; //also hit if a equals b (prefer b)
        if (diff.allPositive()) return 1;

        //compare coefficients, prefer fewer nontrivial ones (other than +1/-1)
        int aCoeffs = 0;
        boolean aHasAbs = false;
        for (Entry<IndefinitePart,BigInteger> entry : pa.getSimpleMonomials().entrySet()) {
            if (entry.getKey().isEmpty()) {
                aHasAbs = !entry.getValue().equals(BigInteger.ZERO);
            } else if (!entry.getValue().abs().equals(BigInteger.ONE)) {
                aCoeffs += 1;
            }
        }

        int bCoeffs = 0;
        boolean bHasAbs = false;
        for (Entry<IndefinitePart,BigInteger> entry : pb.getSimpleMonomials().entrySet()) {
            if (entry.getKey().isEmpty()) {
                bHasAbs = !entry.getValue().equals(BigInteger.ZERO);;
            } else if (!entry.getValue().abs().equals(BigInteger.ONE)) {
                bCoeffs += 1;
            }
        }

        if (aCoeffs > bCoeffs) return 1; //prefer fewer
        if (bCoeffs > aCoeffs) return -1;

        if (aHasAbs && !bHasAbs) return 1; //prefer no absolute coefficients
        if (bHasAbs && !aHasAbs) return -1;

        //this is just a heuristic, no real compare
        return 0;
    }

    //returns true iff aCpx,aPol is heuristically strictly better (i.e. prefer b over a, if not sure)
    public static boolean isFirstCpxBetter(ComplexityValue aCpx, Optional<SimplePolynomial> aPol,
            ComplexityValue bCpx, Optional<SimplePolynomial> bPol)
    {
        int cpxCompare = bCpx.compareTo(aCpx);
        return cpxCompare > 0 ||
               (cpxCompare == 0 && compareBoundsHeuristic(bPol, aPol) > 0);
    }

}
