package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * If `allowFinal` is set and all functions have been analyzed, the overall
 * runtime complexity is computed and the obligation is finally proved.
 * If `allowFinal` is false and all functions have been analyze, the processor
 * returns unsuccessful.
 *
 * Otherwise, the processor replaces function calls on rhss by their
 * size/runtime bounds (inner abstraction) and always succeeds.
 *
 * @author mnaaf
 *
 */
public class CpxRntsResultPropagationProcessor extends ProcessorSkeleton {

    /** Allow the processor to emit a FinalProof
     *  if the ToDo-List is empty?
     */
    private final boolean allowFinal;

    @ParamsViaArgumentObject
    public CpxRntsResultPropagationProcessor(Arguments arguments) {
        this.allowFinal = arguments.allowFinal;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof CpxRntsProblem);
    }

    // abstracts as many inner funapps as possible
    // returns <new TRSTerm, continue/abort-flag[internal]>
    // costs, guards are used as output parameters and are appended
    private Pair<TRSTerm, Boolean> abstractInner(
            TRSTerm term,
            List<SimplePolynomial> costs,
            Set<Constraint> guards,
            CpxRntsProblem rnts)
    {
        if (term.isVariable() || !rnts.hasDefinedSymbols(term)) {
            return new Pair<>(term, true);
        }
        TRSFunctionApplication funapp = (TRSFunctionApplication) term;
        FunctionSymbol fun = funapp.getRootSymbol();

        //abstract arguments first
        List<Pair<TRSTerm, Boolean>> argres = new ArrayList<>();
        for (TRSTerm arg : funapp.getArguments()) {
            argres.add(this.abstractInner(arg, costs, guards, rnts));
        }

        assert funapp.getArguments().size() == funapp.getRootSymbol().getArity();
        assert funapp.getRootSymbol().getArity() == argres.size();

        //collect argument cost and guard
        boolean abstractFurther = true;
        ArrayList<TRSTerm> newArgs = new ArrayList<>();
        for (Pair<TRSTerm, Boolean> arg : argres) {
            newArgs.add(arg.x);
            abstractFurther = abstractFurther && arg.y;
        }

        //abstract this function symbol
        if (abstractFurther && rnts.hasResult(fun)) {
            ComplexitySummary cpx = rnts.getResult(fun);

            // compute cost for the runtime
            TRSTerm newCostTerm = TermHelper.applyBound(rnts, newArgs, cpx.getRuntimePoly());
            SimplePolynomial newCost = TermHelper.termToCost(rnts, newCostTerm);
            costs.add(newCost);

            // replace funapp by free variable, limited by sizebound
            TRSTerm freshVar = rnts.generateFreshVariable("s", false);
            TRSTerm bound = TermHelper.applyBound(rnts, newArgs, cpx.getSizePoly());
            TRSFunctionApplication lower = TRSTerm.createFunctionApplication(CpxIntTermHelper.fGe, freshVar, CpxIntTermHelper.ZERO);
            TRSFunctionApplication upper = TRSTerm.createFunctionApplication(CpxIntTermHelper.fLe, freshVar, bound);
            try {
                guards.add(Constraint.create(lower));
                guards.add(Constraint.create(upper));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e); //internal error
            }
            return new Pair<>(freshVar, true);
        }

        //this function has not been analyzed yet, stop here (unless it's arithmetic)
        assert funapp.getRootSymbol().getArity() == newArgs.size();
        abstractFurther = abstractFurther && !rnts.isDefinedSymbol(funapp.getRootSymbol());
        return new Pair<>(TRSTerm.createFunctionApplication(funapp.getRootSymbol(), newArgs), abstractFurther);
    }

    //wrapper to extend abstractInner to rules
    private RntsRule abstractInner(RntsRule rule, CpxRntsProblem rnts) {
        Set<Constraint> guard = new LinkedHashSet<>();
        ArrayList<SimplePolynomial> costs = new ArrayList<>();
        Pair<TRSTerm,Boolean> abstracted = this.abstractInner(rule.getRight(), costs, guard, rnts);

        //sum up costs
        SimplePolynomial cost = rule.getCost();
        for (SimplePolynomial c : costs) {
            cost = cost.plus(c);
        }

        //collect constraints
        guard.addAll(rule.getConstraints());

        return RntsRule.createUnsafe(rule.getLeft(), abstracted.x, cost, ImmutableCreator.create(guard));
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsProblem rnts = (CpxRntsProblem)obl;

        //check if we can already abort (INF or everything done)
        if (rnts.hasTodo()) {
            for (FunctionSymbol fun : rnts.getTodo()) {
                if (!rnts.hasResult(fun)) continue;
                ComplexitySummary cpx = rnts.getResult(fun);
                if (cpx.hasRuntime() && cpx.getRuntime().equals(ComplexityValue.infinite())) {
                    return ResultFactory.unsuccessful();
                }
            }
        } else {
            //all functions have been analyzed, we can provide a final proof
            if (!this.allowFinal) {
                return ResultFactory.unsuccessful();
            }
            ComplexityValue res = ComplexityValue.constant();
            for (FunctionSymbol fun : rnts.getInitialSymbols()) {
                ComplexitySummary cpx = rnts.getResult(fun);
                assert cpx.hasRuntime();
                res = res.max(cpx.getRuntime());
            }
            return ResultFactory.provedWithValue(ComplexityYNM.createUpper(res), new FinalProof());
        }

        //propagate bounds (replace inner calls by their bounds)
        Set<RntsRule> newRules = new LinkedHashSet<>();
        for (RntsRule rule : rnts.getRules()) {
            newRules.add(this.abstractInner(rule,rnts));
        }

        CpxRntsProblem newObl = rnts.cloneWithNewRules(ImmutableCreator.create(newRules));
        return ResultFactory.proved(newObl, UpperBound.create(), new ResultPropagationProof());
    }


    private static class ResultPropagationProof extends CpxProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Applied inner abstraction using the recently inferred runtime/size bounds where possible.");
        }

    }

    private static class FinalProof extends CpxProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Computed overall runtime complexity");
        }

    }

    public static class Arguments {
        /** Allow the processor to emit a FinalProof
         *  if the ToDo-List is empty?
         */
        public boolean allowFinal = true;
    }

}
