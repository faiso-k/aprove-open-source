package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Implements the improved size abstraction from TRS rules to RNTS rules:
 *
 * - variables are kept: ||x|| = x
 * - non-constant ctors: ||f(t1,...,tn)|| = 1 + ||t1|| + ... + ||tn||
 * - constants are abstracted to different integers, starting at 0
 *   (originally all constants were mapped to 0, but different values
 *   retain more information from the TRS)
 *
 * A rule f(t1,..,tn) -> r is abstracted to f(z1,...,zn) -> ||r|| with guard g,
 * where z1,...,zn are fresh and the guard g contains zi = ||ti|| for all i.
 * The guard also contains x >= 0 for all variables occurring in the rule.
 *
 * Instead of 0, the minimal integer value can also be 1, which can be
 * configured via CpxRntsProblem.MIN_INT_VALUE. Using 0 gives better results.
 *
 * @author mnaaf
 */
public class SizeAbstraction {

    /**
     * Applies size abstraction to transform a TRS rule into a RNTS rule
     *
     * @param rule The TRS rule
     * @param cost The (polynomial) cost of the TRS rule
     * @param argumentNames (modified!) List of fresh names to be used as arguments
     * on the new lhss. If the list is not long enough, it is modified
     * by creating new fresh variables.
     * @param fng used to generate fresh variables for argumentNames
     * @param cpxTrs the TRS problem (needed to count constant constructors)
     *
     * @return a RNTS rule that results from the TRS rule by size abstraction
     * and can thus simulate all evaluations of the TRS rule.
     */
    public static RntsRule abstractRule(
            Rule rule,
            SimplePolynomial cost,
            List<String> argumentNames,
            FreshNameGenerator fng,
            CpxTypedWeightedTrsProblem cpxTrs) {
        //check if we have to add new argument names
        while (rule.getLeft().getArguments().size() > argumentNames.size()) {
            argumentNames.add(fng.getFreshName("z", false));
        }

        // avoid variable name clashes (if rule uses names from argumentNames)
        rule = rule.renameVariables(argumentNames.stream()
                .map(name -> TRSTerm.createVariable(name))
                .collect(Collectors.toSet()));

        // lhs simply gets fresh arguments
        FunctionSymbol root = rule.getRootSymbol();
        ArrayList<TRSVariable> newArgs = new ArrayList<>(root.getArity());
        for (int i=0; i < root.getArity(); ++i) {
            newArgs.add(TRSTerm.createVariable(argumentNames.get(i)));
        }
        TRSFunctionApplication newLhs = TRSTerm.createFunctionApplication(root,newArgs);

        // rhs is size-abstracted
        TRSTerm newRhs = abstractSize(rule.getRight(), cpxTrs);

        // lhs argument sizes are kept as conditions
        Set<Constraint> guard = new HashSet<Constraint>();
        for (int i = 0; i < root.getArity(); ++i) {
            TRSTerm size = abstractSize(rule.getLeft().getArgument(i), cpxTrs);
            TRSFunctionApplication eq = TRSTerm.createFunctionApplication(CpxIntTermHelper.fEq, newArgs.get(i), size);
            try {
                guard.add(Constraint.create(eq));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e); // internal error, cannot occur
            }
        }

        // original variables must be > 0 (or the minimal possible integer value)
        TRSTerm minVal = CpxIntTermHelper.getInteger(CpxRntsProblem.MIN_INT_VALUE);
        for (TRSVariable var : rule.getLeft().getVariables()) {
            TRSFunctionApplication gt = TRSTerm.createFunctionApplication(CpxIntTermHelper.fGe, var, minVal);
            try {
                guard.add(Constraint.create(gt));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e); // internal error, cannot occur
            }
        }
        return RntsRule.createUnsafe(newLhs,newRhs,cost,ImmutableCreator.create(guard));
    }


    /**
     * A hack to check if a given function symbol was introduced as a fresh
     * constant (by the CompletionProcessor). The idea is to abstract all
     * fresh constants to 0 such that their introduction does not influence
     * the size abstraction of other constructors too much.
     *
     * @note this only influences the size abstraction heuristic, so it
     * is irrelevant for the soundness.
     *
     * @return
     */
    private static boolean isFreshConstant(FunctionSymbol fun) {
        return fun.getName().startsWith("null_");
    }

    /**
     * Applies size abstraction to a single term (e.g. the rhs of a rule)
     */
    public static TRSTerm abstractSize(TRSTerm term, CpxTypedWeightedTrsProblem cpxTrs) {
        if (term.isVariable()) {
            return term;
        }

        // function symbols are kept, only arguments are abstracted
        Set<FunctionSymbol> defsyms = cpxTrs.getDefinedSymbols();
        TRSFunctionApplication funapp = (TRSFunctionApplication) term;
        if (defsyms.contains(funapp.getRootSymbol())) {
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            for (TRSTerm arg : funapp.getArguments()) {
                args.add(abstractSize(arg, cpxTrs));
            }
            return TRSTerm.createFunctionApplication(funapp.getRootSymbol(), args);
        }

        // abstract constants to different values to retain more information (improved size abstraction)
        if (funapp.isConstant()) {
            //hack to ignore fresh constants
            if (isFreshConstant(funapp.getRootSymbol())) {
                return CpxIntTermHelper.getInteger(CpxRntsProblem.MIN_INT_VALUE);
            }

            //sort constant constructors
            Type type = cpxTrs.getType(funapp.getRootSymbol()).getReturnType();
            List<FunctionSymbol> ctors = cpxTrs.getConstantConstructors(type).stream().sorted().collect(Collectors.toList());

            //heuristic: if there are no fresh constants, we can make use of 0
            boolean has_null = ctors.stream().anyMatch(f -> f.getName().startsWith("null_"));
            int offset = has_null ? 1 : 0;

            //heuristic: if there are fresh constants, we still make use of 0 if there is only one constant
            if (cpxTrs.hasNonConstantConstructor(type)) {
                offset = 0; //ensure start at 0 (for instance to model peano numbers correctly)
            }

            //use index of funapp in ctors as its size abstraction
            int i=0;
            for (FunctionSymbol fun : ctors) {
                if (isFreshConstant(fun)) continue;
                if (fun.equals(funapp.getRootSymbol())) break;
                i += 1;
            }
            assert(i < ctors.size());
            BigInteger res = BigInteger.valueOf(offset + i).add(CpxRntsProblem.MIN_INT_VALUE.getBigInt());
            return CpxIntTermHelper.getInteger(BigIntImmutable.create(res));
        } else {
            // non-constant ctors are abstracted to 1 + arguments
            TRSTerm result = CpxIntTermHelper.ONE;
            for (int i = 0; i < funapp.getRootSymbol().getArity(); ++i) {
                TRSTerm arg = abstractSize(funapp.getArgument(i), cpxTrs);
                result = TRSTerm.createFunctionApplication(CpxIntTermHelper.fAdd, result, arg);
            }
            return result;
        }
    }

}
