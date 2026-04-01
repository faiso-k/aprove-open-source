package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.ComplexitySummary.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms the RNTS into an ITS to obtain a runtime bound for a single function.
 * Inner function calls must already have been replaced by their size/runtime bounds
 * (by the ResultPropagation processor). Outer function calls (outside of the
 * target function) are replaced by their previously obtained runtime bounds
 * by this processor. Note that to apply these runtime bounds, we need to know
 * a size bound for the target function. Hence the SizeProcessor must be used first.
 *
 * The runtime bound is then directly obtained by using an IntTrsBackend.
 *
 * @note SizeProcessor must be run before this processor!
 *
 * @param abortOnInf If this option is true, then the processor aborts immediately
 * after an INF runtime bound was inferred (i.e. without analyzing all functions
 * of the current SCC and without removing the SCC from the todo list).
 *
 * @author mnaaf
 *
 */
public class CpxRntsRuntimeProcessor extends ProcessorSkeleton {

    //options
    private final boolean abortOnInf;
    private final IntTrsBackendSpawner.Timeouts timeouts;

    //arguments that can be passed from the strategy file
    public static class Arguments {
        //abort when runtime bound INF (i.e. no bound) occurs for any function in the SCC
        //(this is required to make use of the RetryProcessor and avoids unnecessary computations)
        public boolean abortOnInf = true;

        //timeout for the ITS backends
        public int pubsTimeout = 3000;
        public int koatTimeout = 6000;
        public int coflocoTimeout = 4000;
    }

    @ParamsViaArgumentObject
    public CpxRntsRuntimeProcessor(final Arguments arguments) {
        this.abortOnInf = arguments.abortOnInf;

        this.timeouts = new IntTrsBackendSpawner.Timeouts();
        this.timeouts.pubs = arguments.pubsTimeout;
        this.timeouts.koat = arguments.koatTimeout;
        this.timeouts.cofloco = arguments.coflocoTimeout;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!IntTrsBackendSpawner.anyBackendInstalled()) return false;
        if (!(obl instanceof CpxRntsProblem)) return false;

        //check that there is some work to do
        CpxRntsProblem rnts = (CpxRntsProblem)obl;
        if (!rnts.hasTodo()) return false;

        //check if all size bounds for this SCC are available
        //(this does not include size bounds from earlier SCCs,
        //but checks if SizeProcessor was already called on this SCC)
        return rnts.getTodo().stream().allMatch(f -> rnts.hasResult(f) && rnts.getResult(f).hasSize());
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsRuntimeWorker worker = new CpxRntsRuntimeWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private class CpxRntsRuntimeWorker {
        //state
        private CpxRntsProblem rnts = null;
        private FunctionSymbol goal = null; //the function symbol to be analyzed
        private FunctionSymbol start = null;
        private FunctionSymbol sink = null;

        private void generateSpecialLocations() {
            FreshNameGenerator fng = new FreshNameGenerator(this.rnts.getDefinedSymbols(), FreshNameGenerator.VARIABLES);
            this.start = FunctionSymbol.create(fng.getFreshName("start", false), this.goal.getArity());
            this.sink = FunctionSymbol.create(fng.getFreshName("sink", false), 0);
        }

        /**
         * Substitutes outer function applications by their size bounds
         * @param cost modified to accumulate the runtime costs of removed funapps
         * @param newRhss modified to collect all funapps not yet analyzed
         * @return the resulting size bound (used internally)
         */
        private TRSTerm inlineOuter(TRSTerm term, List<SimplePolynomial> costs, List<TRSFunctionApplication> newRhss) {
            if (term.isVariable()) {
                return term;
            }

            TRSFunctionApplication funapp = (TRSFunctionApplication)term;
            FunctionSymbol fun = funapp.getRootSymbol();
            if (rnts.isDefinedSymbol(fun)) {
                assert rnts.hasResult(fun); //size must have been analyzed before
                ComplexitySummary cpx = rnts.getResult(fun);
                assert cpx.hasSize();
                if (!cpx.hasRuntime()) {
                    newRhss.add(funapp); //this funapp needs to be analyzed now
                    return TermHelper.applyBound(rnts,funapp.getArguments(),cpx.getSizePoly());
                }
            }

            //abstract arguments first
            ArrayList<TRSTerm> sizes = new ArrayList<>();
            for (TRSTerm arg : funapp.getArguments()) {
                TRSTerm sizebound = inlineOuter(arg, costs, newRhss);
                sizes.add(sizebound);
            }

            //evaluate arithmetic (apply to obtained size bounds)
            if (!rnts.isDefinedSymbol(fun)) {
                assert CpxIntTermHelper.getIntegerValue(funapp) != null || CpxIntTermHelper.polySyms.contains(fun);
                return TRSTerm.createFunctionApplication(fun, sizes);
            }

            //apply known runtime and size bound
            ComplexitySummary cpx = rnts.getResult(fun);
            TRSTerm newCost = TermHelper.applyBound(rnts, sizes, cpx.getRuntimePoly());
            TRSTerm newSize = TermHelper.applyBound(rnts, sizes, cpx.getSizePoly());
            costs.add(TermHelper.termToCost(rnts,newCost));
            return newSize;
        }


        //lifts inlineOuter to rules, takes care of sink/COM_n application for rhs
        private RntsRule abstractRule(RntsRule rule) {
            ArrayList<SimplePolynomial> newCosts = new ArrayList<>();
            ArrayList<TRSFunctionApplication> newRhss = new ArrayList<>();
            inlineOuter(rule.getRight(), newCosts, newRhss);

            SimplePolynomial totalCost = rule.getCost();
            for (SimplePolynomial c : newCosts) {
                totalCost = totalCost.plus(c);
            }

            TRSTerm rhs;
            if (newRhss.isEmpty()) {
                rhs = TRSTerm.createFunctionApplication(this.sink);
            } else if (newRhss.size() == 1) {
                rhs = newRhss.get(0);
            } else {
                rhs = CpxIntTermHelper.createCom(newRhss);
            }
            return RntsRule.createUnsafe(rule.getLeft(), rhs, totalCost, rule.getConstraints());
        }

        //creates rule "start(..) -> goal(..) :|: vars >= 0
        private RntsRule makeStartRule() {
            ArrayList<TRSTerm> args = new ArrayList<>();
            for (int i=0; i < this.goal.getArity(); ++i) {
                args.add(TRSTerm.createVariable(rnts.getArgumentName(i)));
            }

            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(this.start, args);
            TRSTerm rhs = TRSTerm.createFunctionApplication(this.goal, args);

            Set<Constraint> guard = new HashSet<>();
            TRSTerm minVal = CpxIntTermHelper.getInteger(CpxRntsProblem.MIN_INT_VALUE);
            for (TRSTerm arg : args) {
                guard.add(TermHelper.makeGreaterEqualConstraint(arg,minVal));
            }
            return RntsRule.createUnsafe(lhs, rhs, SimplePolynomial.ZERO, ImmutableCreator.create(guard));
        }

        public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
                throws AbortionException {
            IntTrsBoundProofBuilder proofBuilder = new IntTrsBoundProofBuilder(CpxType.Runtime);
            this.rnts = (CpxRntsProblem) obl;
            assert this.rnts.hasAnalysisOrder();
            assert this.rnts.hasTodo();
            boolean aborted = false;

            for (FunctionSymbol todofun : this.rnts.getTodo()) {
                this.goal = todofun;
                assert this.goal != null;
                this.generateSpecialLocations();

                //abstract all relevant rules
                Set<RntsRule> newRules = new HashSet<>();
                Set<RntsRule> relevantRules = DependentRules.getTodoRuleClosureFrom(goal, this.rnts);
                for (RntsRule rule : relevantRules) {
                    newRules.add(this.abstractRule(rule));

                }
                //generate special rules
                newRules.add(this.makeStartRule());

                CpxRntsProblem abstractedITS = this.rnts.cloneWithNewRules(
                        ImmutableCreator.create(newRules),
                        ImmutableCreator.create(Collections.singleton(this.start)));

                //simplify costs due to weaknesses in KoAT
                CpxRntsProblem simplifiedITS = CostSimplification.apply(abstractedITS);

                IntTrsBackend solver = IntTrsBackendSpawner.runAll(simplifiedITS, aborter, CpxRntsRuntimeProcessor.this.timeouts);
                ComplexityValue newCpx = solver.getComplexity();
                Optional<SimplePolynomial> newPoly = solver.getPolynomialBound();

                ComplexitySummary cpxres = this.rnts.getResult(this.goal).update(CpxType.Runtime, newCpx, newPoly);
                this.rnts = this.rnts.cloneWithUpdatedResult(this.goal, cpxres);
                proofBuilder.add(this.goal, cpxres, simplifiedITS, solver);

                //abort early when we fail to find a bound
                if (CpxRntsRuntimeProcessor.this.abortOnInf && newCpx.equals(ComplexityValue.infinite())) {
                    aborted = true;
                    break;
                }
            }

            CpxRntsProblem newObl = this.rnts;
            if (!aborted) {
                newObl = this.rnts.cloneWithTodoDone(); //all functions analyzed without INF bound (or we chose to not abort)
            }
            return ResultFactory.proved(newObl, UpperBound.create(), proofBuilder.buildProof());
        }
    }
}
