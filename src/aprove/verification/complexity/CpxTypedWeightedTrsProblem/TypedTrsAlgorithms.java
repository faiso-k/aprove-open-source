package aprove.verification.complexity.CpxTypedWeightedTrsProblem;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Checks if a given TypedTrs is completely defined,
 * i.e. if for every defined symbol and all type-correct argument terms,
 * there exists an applicable rewrite rule.
 *
 * @note the current implementation ignores non-left-linear rules, so it
 * may return false even though a non-left-linear TRS is completely defined.
 *
 * @author mnaaf
 *
 */
public abstract class TypedTrsAlgorithms {

    //checks if the given set of term-tuples is complete for the given type-tuple
    //note that this requires to check all combinations of ctors for this type, so it's quite expensive
    private static boolean isComplete(Set<List<TRSTerm>> terms, List<Type> types, CpxTypedWeightedTrsProblem trs) {
        if (terms.isEmpty()) {
            return false;
        }

        outer: for (List<TRSTerm> args : terms) {
            for (TRSTerm arg : args) {
                if (!arg.isVariable()) continue outer;
            }
            return true;
        }

        //collect all ctors for the different types (we need some order for iteration)
        List<List<FunctionSymbol>> ctorlists = new ArrayList<>(types.size());
        for (Type t : types) {
            List<FunctionSymbol> l = new ArrayList<>();
            l.addAll(trs.getConstantConstructors(t));
            l.addAll(trs.getNonConstantConstructors(t));
            ctorlists.add(l);
        }

        //iterate over all combinations of ctors, start with the first tuple
        int[] ctors = new int[types.size()];
        for (int i=0; i < ctors.length; ++i) {
            ctors[i] = 0;
        }

        while (true) {
            //find all terms matching a concrete ctor combination
            Set<List<TRSTerm>> relevant = new LinkedHashSet<>();
            for (List<TRSTerm> args : terms) {
                assert args.size() == types.size();
                boolean isrelevant = true;
                for (int i=0; i < types.size(); ++i) {
                    if (!args.get(i).isVariable()) {
                        assert !ctorlists.get(i).isEmpty(); //non-variables means a type must be inferred
                        FunctionSymbol argsym = ((TRSFunctionApplication)args.get(i)).getRootSymbol();
                        FunctionSymbol ctorsym = ctorlists.get(i).get(ctors[i]);
                        if (!argsym.equals(ctorsym)) {
                            isrelevant = false;
                            break;
                        }
                    }
                }
                if (isrelevant) {
                    relevant.add(args);
                }
            }

            //if this combination is not matched at all
            if (relevant.isEmpty()) {
                return false;
            }

            //for all non-constant ctors: continue check recursively
            ctorloop: for (int i=0; i < types.size(); ++i) {
                if (ctorlists.get(i).isEmpty()) continue;
                FunctionSymbol ctorsym = ctorlists.get(i).get(ctors[i]);
                if (ctorsym.getArity() == 0) continue;

                Set<List<TRSTerm>> ctorargs = new LinkedHashSet<>();
                for (List<TRSTerm> args : relevant) {
                    if (args.get(i).isVariable()) continue ctorloop;
                    ctorargs.add(((TRSFunctionApplication)args.get(i)).getArguments());
                }

                if (!isComplete(ctorargs, trs.getArgumentTypes(ctorsym), trs)) {
                    return false;
                }
            }

            //check the next combination of ctors (similar to incrementing a bitvector)
            int j = ctors.length-1;
            while (j >= 0 && ctors[j]+1 >= ctorlists.get(j).size()) {
                ctors[j] = 0;
                j -= 1;
            }
            if (j < 0) {
                return true;
            }
            ctors[j] += 1;
        }
    }

    /**
     * Returns true iff the given function is completely defined w.r.t. correctly typed arguments
     * @note non-linear rules are ignored, so this is sound only for left-linear TRS (see below)
     */
    public static boolean isFunCompletelyDefined(FunctionSymbol fun, CpxTypedWeightedTrsProblem trs) {
        Set<Rule> funRules = trs.getUnweightedRulesFor(fun);
        Set<List<TRSTerm>> funArgs = new LinkedHashSet<>();
        for (Rule rule : funRules) {
            if (rule.getLeft().isLinear()) { //ignore nonlinear rules
                funArgs.add(rule.getLeft().getArguments());
            }
        }
        if (!isComplete(funArgs, trs.getArgumentTypes(fun), trs)) {
            return false;
        }
        return true;
    }

    /**
     * Checks whether the given TRS is completely defined w.r.t correctly typed terms.
     * @note this check works for left-linear TRS. Rules that are not left-linear
     * are simply ignored otherwise (thus "false" is not meaningful)
     */
    public static boolean isCompletelyDefined(CpxTypedWeightedTrsProblem trs) {
        for (FunctionSymbol fun : trs.getDefinedSymbols()) {
            if (!isFunCompletelyDefined(fun, trs)) {
                return false;
            }
        }
        return true;
    }

}
