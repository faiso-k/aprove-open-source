package aprove.verification.complexity.CpxTypedWeightedTrsProblem.Processors;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 * This processor is applicable to constructor systems and ensures several
 * properties that are needed for the soundness of the conversion from a TRS
 * into a RNTS. These properties are:
 *
 * (1) every type has a constant constructor, and
 *
 * (2) all functions for which relative rules (of weight 0) exist
 *     (i.e. functions f where f(...) -> ... is a rule with weight 0)
 *     are completely defined, and
 *
 * (3) Either
 *     (a) critical functions, or
 *     (b) all functions
 *     are completely defined.
 *
 * A function is completely defined if it is applicable to all well-typed
 * ground terms. A function can be made complete by adding a rule like
 *
 *   f(v0,..,vn) -> c      for fresh variables v0,...,vn
 *
 * where "c" is a fresh or any existing (type-correct) constant.
 *
 * A function is called critical iff it can occur inside another function
 * (in a derivation starting from a basic term).
 *
 * @author mnaaf
 */
public class CpxTypedWeightedTrsCompletionProcessor extends CpxTypedWeightedTrsProcessor {

    private final boolean completeAll;
    private final boolean alwaysFresh;

    //arguments that can be passed from the strategy file
    public static class Arguments {
        //complete all functions (instead of only the "critical" ones)
        public boolean completeAll = false;

        //always use fresh constants c when adding rules f(x1,...,xn) -> c
        //if false, a heuristic is used to choose between a fresh and an existing constant
        public boolean alwaysFresh = false;
    }

    @ParamsViaArgumentObject
    public CpxTypedWeightedTrsCompletionProcessor(final Arguments arguments) {
        this.completeAll = arguments.completeAll;
        this.alwaysFresh = arguments.alwaysFresh;
    }

    //collect functions that inside any other function in term
    private static void addInnerFunctions(TRSTerm term, Set<FunctionSymbol> critical, CpxTypedWeightedTrsProblem trs) {
        if (term.isVariable()) return;
        TRSFunctionApplication funapp = (TRSFunctionApplication)term;
        if (trs.isDefined(funapp.getRootSymbol())) {
            //all defined symbols that are inside funapp are critical
            for (TRSTerm arg : funapp.getArguments()) {
                for (FunctionSymbol fun : arg.getFunctionSymbols()) {
                    if (trs.isDefined(fun)) {
                        critical.add(fun);
                    }
                }
            }
        } else {
            //if this is a constructor, recurse into arguments
            for (TRSTerm arg : funapp.getArguments()) {
                addInnerFunctions(arg, critical, trs);
            }
        }
    }

    //closure: if  f  is critical and  f -> r  is a rule, then all defined symbols in  r  are also critical
    private static boolean closureUnderRule(Rule rule, Set<FunctionSymbol> critical, CpxTypedWeightedTrsProblem trs) {
        if (critical.contains(rule.getRootSymbol())) {
            Set<FunctionSymbol> addFuns = rule.getRight().getFunctionSymbols();
            addFuns.retainAll(trs.getDefinedSymbols());
            return critical.addAll(addFuns); //true iff changed
        }
        return false;
    }

    private static FunctionSymbol createNullConstant(FunctionSymbol fun, FreshNameGenerator fng) {
        return FunctionSymbol.create(fng.getFreshName("null_"+fun.getName(), false), 0);
    }

    private static FunctionSymbol getExistingConstant(FunctionSymbol fun, CpxTypedWeightedTrsProblem trs) {
        Set<FunctionSymbol> ctors = trs.getConstantConstructors(trs.getType(fun).getReturnType());
        assert(!ctors.isEmpty());
        return ctors.iterator().next();
    }

    //creates a rule used to make fun complete
    private static WeightedRule buildNullRule(FunctionSymbol fun, FunctionSymbol nullCtor) {
        //choose arbitrary variable names (fresh is not needed)
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (int i=0; i < fun.getArity(); ++i) {
            args.add(TRSTerm.createVariable("v"+i));
        }
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fun, args);
        TRSTerm rhs = TRSTerm.createFunctionApplication(nullCtor);
        return WeightedRule.create(lhs, rhs, 0);
    }

    //creates a rule fun(x1,...,xn) -> c where c is heuristically chosen to be a fresh or an existing constant
    private static WeightedRule buildCompletingRule(FunctionSymbol fun, FreshNameGenerator fng,
            CpxTypedWeightedTrsProblem trs, boolean alwaysFresh) {
        //heuristic: use existing ctor if there is only one constant ctor, otherwise fresh one
        if (alwaysFresh || trs.getConstantConstructors(trs.getType(fun).getReturnType()).size() > 1) {
            return buildNullRule(fun,createNullConstant(fun,fng));
        } else {
            return buildNullRule(fun,getExistingConstant(fun,trs));
        }
    }

    private static CpxTypedWeightedTrsProblem cloneWithAddedRules(
            CpxTypedWeightedTrsProblem trs, Set<WeightedRule> addRules) {
        Set<WeightedRule> newRules = new LinkedHashSet<>();
        newRules.addAll(trs.getRules());
        newRules.addAll(addRules);
        CpxWeightedTrsProblem newTrs = CpxWeightedTrsProblem.create(ImmutableCreator.create(newRules), trs.isInnermost());

        //perform a new type inference (new rules) and ensure that all types have constant ctors
        CpxTypedWeightedTrsProblem res = TypeInference.inferTypes(newTrs);
        return res.cloneWithConstantConstructors();
    }

    @Override
    protected Result processCpxTypedWeightedTrs(CpxTypedWeightedTrsProblem trs, Abortion aborter) throws AbortionException {
        //remember constant ctors for proof output
        Set<FunctionSymbol> originalConstants = trs.getConstantConstructors();

        //fng to create fresh constants
        FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.PROLOG_FUNCS);
        fng.lockHasNames(CollectionUtils.getFunctionSymbols(trs.getRules()));


        /*
         * (1) ensure that all types have a constant constructor
         */
        trs = trs.cloneWithConstantConstructors();


        //store information for proof output
        Set<WeightedRule> addedRules = new LinkedHashSet<>();

        //determine all function symbols that have to be completely defined for soundness
        Set<FunctionSymbol> criticalFuns = new LinkedHashSet<>();
        Set<Rule> rules = trs.getUnweightedRules();

        if (this.completeAll) {
            criticalFuns.addAll(trs.getDefinedSymbols());
        } else {
            //find critical functions
            for (Rule rule : rules) {
                addInnerFunctions(rule.getRight(), criticalFuns, trs);
            }

            //close critical functions under "rule closure"
            boolean changed = true;
            while (changed) {
                changed = false;
                for (Rule rule : rules) {
                    if (closureUnderRule(rule, criticalFuns, trs)) {
                        changed = true;
                    }
                }
            }
        }


        /*
         * (2) check functions for which relative rules exist
         */
        Set<FunctionSymbol> forceCompletion = new LinkedHashSet<>();
        for (WeightedRule rule : trs.getRules()) {
            if (rule.getWeight().intValue() == 0) {
                forceCompletion.add(rule.getRootSymbol());
            }
        }
        if (!forceCompletion.isEmpty()) {
            Set<WeightedRule> addRules = new LinkedHashSet<>();
            for (FunctionSymbol fun : forceCompletion) {
                addRules.add(buildCompletingRule(fun, fng, trs, this.alwaysFresh));
            }

            addedRules.addAll(addRules);
            trs = cloneWithAddedRules(trs, addRules);
            criticalFuns.removeAll(forceCompletion);
        }


        //remember the critical/uncritical functions for proof output
        Set<FunctionSymbol> proofCritical = new LinkedHashSet<>(criticalFuns);
        proofCritical.addAll(forceCompletion);

        Set<FunctionSymbol> proofUncritical = new LinkedHashSet<>(trs.getDefinedSymbols());
        proofUncritical.removeAll(proofCritical);


        /*
         * (3) add rules (and recreate type information) to complete all critical functions
         */
        boolean changed = true;
        while (changed) {
            changed = false;
            Set<FunctionSymbol> stillCritical = new LinkedHashSet<>();

            //add rules to ensure that all critical functions are completely defined
            Set<WeightedRule> addRules = new LinkedHashSet<>();
            for (FunctionSymbol fun : criticalFuns) {
                if (!TypedTrsAlgorithms.isFunCompletelyDefined(fun, trs)) {
                    changed = true;
                    addRules.add(buildCompletingRule(fun, fng, trs, this.alwaysFresh));
                } else {
                    stillCritical.add(fun);
                }
            }
            addedRules.addAll(addRules);
            trs = cloneWithAddedRules(trs, addRules);
            criticalFuns = stillCritical;
        }

        //add information about added fresh constants to the proof
        Set<FunctionSymbol> freshConstants = trs.getConstantConstructors();
        freshConstants.removeAll(originalConstants);

        //return a CompleteTrs to indicate the completion property in the obligation
        CpxTypedWeightedCompleteTrsProblem res = new CpxTypedWeightedCompleteTrsProblem(trs, !this.completeAll);
        return ResultFactory.proved(res, UpperBound.create(), new CompletionProof(proofCritical,proofUncritical,addedRules,freshConstants,this.completeAll));
    }

    @Override
    protected boolean isCpxTypedWeightedTrsApplicable(CpxTypedWeightedTrsProblem obl) {
        return obl.isConstructorSystem();
    }

    private static class CompletionProof extends CpxProof {
        private final Set<FunctionSymbol> freshConstants;
        private final Set<FunctionSymbol> criticalFuns;
        private final Set<FunctionSymbol> uncriticalFuns;
        private final Set<WeightedRule> addedRules;
        private final boolean completeAll;

        public CompletionProof(Set<FunctionSymbol> c, Set<FunctionSymbol> u, Set<WeightedRule> rs, Set<FunctionSymbol> f, boolean all) {
            criticalFuns = c;
            uncriticalFuns = u;
            freshConstants = f;
            completeAll = all;
            addedRules = rs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            if (this.completeAll) {
                s.append(o.escape("The TRS is a completely defined constructor system, as every type has a constant constructor and the following rules were added:"));
            } else {
                s.append(o.escape("The transformation into a RNTS is sound, since:") + o.paragraph());
                s.append(o.escape("(a) The obligation is a constructor system where every type has a constant constructor,") + o.paragraph());

                s.append(o.escape("(b) The following defined symbols do not have to be completely defined, as they can never occur inside other defined symbols:"));
                s.append(o.cond_linebreak());
                s.append(o.set(uncriticalFuns, Export_Util.RULES));
                s.append(o.cond_linebreak());

                s.append(o.escape("(c) The following functions are completely defined:"));
                s.append(o.cond_linebreak());
                s.append(o.set(criticalFuns, Export_Util.RULES));
                s.append(o.cond_linebreak());
                s.append(o.escape("Due to the following rules being added:"));
            }
            s.append(o.cond_linebreak());
            s.append(o.set(addedRules, Export_Util.RULES));
            s.append(o.cond_linebreak());

            s.append(o.escape("And the following fresh constants: "));
            s.append(o.set(freshConstants, Export_Util.NICE_SET));
            s.append(o.cond_linebreak());
            return s.toString();
        }
    }
}
