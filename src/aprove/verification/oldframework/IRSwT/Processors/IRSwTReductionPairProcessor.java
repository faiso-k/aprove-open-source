package aprove.verification.oldframework.IRSwT.Processors;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A processor based on reduction pair search for QDP problems. Uses existing
 * QDPActiveSolvers (i.e., the workhorses of the QDPReductionPairProcessor)
 * to search for all kinds of reduction pairs (i.e., orders). Temporarily
 * filters away integer stuff, so no issues with "bounded" will arise.
 *
 * Distinct feature: Does /not/ require that after the filtering variables
 * on right-hand sides of "rules" also occur on left-hand sides.
 * QDPActiveSolvers do not have any problem with that -- they *automatically*
 * determine an argument filtering which ensures this property.
 *
 * @author Carsten Fuhs
 */
public class IRSwTReductionPairProcessor extends Processor.ProcessorSkeleton {
    /** Some arguments. */
    private final Arguments arguments;

    /** Some arguments */
    public static class Arguments {
        /** Order your order here! */
        public SolverFactory order;
        /** Orient all rules strictly in a single go? */
        public boolean allstrict;
    }

    /**
     * Constructor!
     *
     * @param arguments configuration data from the strategy
     */
    @ParamsViaArgumentObject
    public IRSwTReductionPairProcessor(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        // 1. Get ready:
        assert obl instanceof IRSwTProblem : "Wrong obligation!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        final ImmutableSet<IGeneralizedRule> oldIRules = irswt.getRules();

        // 2. Deduce the sorts:
        final SortAnalyzer sortAnalyzer = new SortAnalyzer(oldIRules);
        final SortDictionary sorts = sortAnalyzer.analyze();

        // 3. Apply filter:
        final AbstractFilter filter = new RemoveIntFilter(oldIRules, sorts, fng);
        filter.applyFilter();
        final Map<GeneralizedRule, List<IGeneralizedRule>> filteredRules = IRSwTReductionPairProcessor.iGenRulesToGenRules(oldIRules, filter);
        final boolean useAllstrict = this.arguments.allstrict || filteredRules.size() == 1;

        // 4. Synthesize a suitable order:
        final QActiveSolver solver = this.arguments.order.getQActiveSolver();

        final Set<GeneralizedRule> copiedGenRules = new LinkedHashSet<>(filteredRules.keySet());
        final QActiveOrder order = solver.solveQActive(copiedGenRules,
            java.util.Collections.<Rule, QActiveCondition>emptyMap(),
            false, useAllstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        // 5. Generate the new problem:

        LinkedHashSet<IGeneralizedRule> newIRules = new LinkedHashSet<>();
        LinkedHashSet<IGeneralizedRule> deletedIRules = new LinkedHashSet<>();
        for (Entry<GeneralizedRule, List<IGeneralizedRule>> filteredRuleToIRules : filteredRules.entrySet()) {
            GeneralizedRule rule = filteredRuleToIRules.getKey();
            TRSTerm left = rule.getLeft();
            TRSTerm right = rule.getRight();
            if (! order.inRelation(left, right)) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> lGEr = Constraint.fromRule(rule, OrderRelation.GE);
                    assert order.solves(lGEr) : order + " does not solve " + lGEr;
                }
                newIRules.addAll(filteredRuleToIRules.getValue());
            } else {
                deletedIRules.addAll(filteredRuleToIRules.getValue());
            }
        }
        if (Globals.useAssertions) {
            assert ! deletedIRules.isEmpty() : "No rule deleted!";
        }

        final IRSwTProblem newProb = new IRSwTProblem(ImmutableCreator.create(newIRules));
        return ResultFactory.proved(newProb, YNMImplication.EQUIVALENT,
            new IRSwTReductionPairProof(filteredRules, order, filter, sorts, deletedIRules));
    }

    /**
     *
     * @param iRules of shape l -> r | cond where l and r must not contain any
     *  predefined integer symbols
     * @param filter used to filter away numbers
     * @return rules which are like iRules, but only use classic term rewriting
     *  (except that we allow variables that occur on the right, but not on the
     *  left); cond suspiciously got lost on the way
     * @throws AbortionException
     */
    private static Map<GeneralizedRule, List<IGeneralizedRule>> iGenRulesToGenRules(final Set<IGeneralizedRule> iRules,
                        final AbstractFilter filter) throws AbortionException {
        final Map<GeneralizedRule, List<IGeneralizedRule>> res = new LinkedHashMap<>();
        for (IGeneralizedRule iRule : iRules) {
            IGeneralizedRule filteredIRule = filter.getNewRule(iRule);
            TRSFunctionApplication left = filteredIRule.getLeft();
            TRSTerm right = filteredIRule.getRight();
            GeneralizedRule rule = GeneralizedRule.create(left, right);
            List<IGeneralizedRule> ruleIRules = res.get(rule);
            if (ruleIRules == null) {
                ruleIRules = new ArrayList<>();
                res.put(rule, ruleIRules);
            }
            ruleIRules.add(iRule);
        }
        return res;
    }

    /**
     * A truly bewildering proof!
     */
    class IRSwTReductionPairProof extends DefaultProof {
        /** Map of filtered rules to corresponding original iRules */
        private final Map<GeneralizedRule, List<IGeneralizedRule>> filteredRules;
        /** The order we found! */
        private final QActiveOrder order;
        /** The filter used before searching for the order. */
        private final AbstractFilter preFilter;
        /** The sort dictionary used by the filter. */
        private final SortDictionary sorts;
        /** Deleted rules! */
        private final Set<IGeneralizedRule> deletedIRules;

        /**
         * Based on an order we create a proof!
         * @param filteredRules order search was done for its keys, representing its values
         * @param order some order
         * @param preFilter filtered the integers away
         * @param sorts the sort dictionary
         * @param deletedIRules the rules that were oriented strictly
         */
        public IRSwTReductionPairProof(final Map<GeneralizedRule, List<IGeneralizedRule>> filteredRules,
                final QActiveOrder order, final AbstractFilter preFilter, final SortDictionary sorts,
                final Set<IGeneralizedRule> deletedIRules) {
            this.filteredRules = filteredRules;
            this.order = order;
            this.preFilter = preFilter;
            this.sorts = sorts;
            this.deletedIRules = deletedIRules;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            StringBuilder res = new StringBuilder();
            res.append("We use the reduction pair processor ");
            res.append(eu.cite(new Citation[]{Citation.LPAR04,Citation.JAR06}));
            res.append(" on an integer-free filtered version of the IRSwT.");
            res.append(eu.export("Filter to remove integers:")).append(eu.linebreak()).append(eu.cond_linebreak());
            res.append(this.preFilter.export(eu)).append(eu.linebreak()).append(eu.cond_linebreak());
            res.append(eu.export("Sort dictionary:")).append(eu.linebreak()).append(eu.cond_linebreak());
            res.append(this.sorts.export(eu)).append(eu.linebreak()).append(eu.cond_linebreak());
            res.append(eu.export("Mapping filtered rules to original rules with integers:"));
            for (Entry<GeneralizedRule, List<IGeneralizedRule>> ruleToIRule : this.filteredRules.entrySet()) {
                res.append(eu.linebreak()).append(eu.cond_linebreak());
                res.append(ruleToIRule.getKey().export(eu)).append(eu.linebreak());
                res.append(eu.fontcolor("stands for", Color.GRAY));
                res.append(eu.linebreak()).append(eu.escape("["));
                boolean first = true;
                for (IGeneralizedRule iRule : ruleToIRule.getValue()) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(eu.preFormatted(", ")).append(eu.linebreak());
                    }
                    res.append(iRule.export(eu));
                }
                res.append(eu.escape("]"));
            }
            res.append(eu.linebreak()).append(eu.cond_linebreak());
            res.append(eu.export("Order on filtered rules:")).append(eu.linebreak());
            res.append(this.order.export(eu));
            res.append(eu.linebreak());
            res.append("Strictly oriented rules:").append(eu.linebreak());
            res.append(eu.set(this.deletedIRules, Export_Util.RULES));
            return res.toString();
        }
    }
}
