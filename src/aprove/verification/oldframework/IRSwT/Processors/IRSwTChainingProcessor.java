package aprove.verification.oldframework.IRSwT.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Applies chaining. This merge two rules into a single one.
 * @author Matthias Hoelzel
 *
 */
public class IRSwTChainingProcessor extends Processor.ProcessorSkeleton {
    /** Some arguments */
    public static class Arguments {
        /** Order your order here!*/
        public ChainingMode mode = ChainingMode.REMOVE_LOOPS;
    }

    /** Some arguments. */
    private final Arguments arguments;

    /**
     * Constructor!
     * @param args given arguments
     */
    @ParamsViaArgumentObject
    public IRSwTChainingProcessor(final Arguments args) {
        this.arguments = args;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (!Options.certifier.isNone()) {
            return false;
        }
        if (!(obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded())) {
            return false;
        }
        return (!this.arguments.mode.equals(ChainingMode.REMOVE_LOOPS) || ((IRSwTProblem) obl).getTerminationDigraph() != null);
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
        final PartiallyComputedDigraph<IGeneralizedRule> originalGraph = irswt.getTerminationDigraph();
        final PartiallyComputedDigraph<IGeneralizedRule> digraph;
        if (originalGraph != null) {
            digraph = new PartiallyComputedDigraph<>(originalGraph);
            digraph.overestimate();
        } else {
            digraph = null;
        }

        // 2. Apply some chaining:
        final IRSwTProblem newProblem = this.applyChaining(aborter, irswt, digraph);
        if (newProblem == null) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT, new IRSwTChainingProof());
    }

    private IRSwTProblem applyChaining(
        final Abortion aborter,
        final IRSwTProblem irswt,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph) throws AbortionException
    {
        switch (this.arguments.mode) {
        case SINGLE_RULE:
            return this.simpleChaining(aborter, irswt, digraph);
        case REMOVE_LOOPS:
            return this.removeLoopsChaining(aborter, irswt, digraph);
        default:
            return null;
        }
    }

    /**
     * @param aborter
     * @param irswt
     * @param digraph
     * @return
     * @throws AbortionException
     */
    private IRSwTProblem simpleChaining(
        final Abortion aborter,
        final IRSwTProblem irswt,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph) throws AbortionException
    {
        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>();
        final IGeneralizedRule pickedRule = irswt.getRules().iterator().next();
        if (digraph != null) {
            digraph.removeVertex(pickedRule);
        }
        this.simpleChaining(pickedRule, aborter, irswt, digraph, newRules);
        if (digraph != null) {
            digraph.freeze();
        }
        return new IRSwTProblem(ImmutableCreator.create(newRules), digraph);
    }

    /**
     * Performs chaining.
     * @param pickedRule start to concat with other rules
     * @param aborter some aborter
     * @param irswt our rule system
     * @param digraph copy of problems digraph or null. If != null, then
     * we can add some non-edges to it.
     * @param newRules set of new rules
     * @throws AbortionException can be aborted
     */
    private void simpleChaining(
        final IGeneralizedRule pickedRule,
        final Abortion aborter,
        final IRSwTProblem irswt,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph,
        final LinkedHashSet<IGeneralizedRule> newRules) throws AbortionException
    {
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        for (final IGeneralizedRule otherRule : irswt.getRules()) {
            if (otherRule != pickedRule) {
                newRules.add(otherRule);
            }
            if (digraph != null) {
                if (digraph.isEvaluated(pickedRule, otherRule) && !digraph.isConnected(pickedRule, otherRule)) {
                    // We can skip this rule.
                    continue;
                }
            }
            final Chaining chaining = new Chaining(pickedRule, otherRule, fng, aborter);
            final IGeneralizedRule newRule = chaining.applyChaining();
            if (newRule != null && !ToolBox.buildFalse().equals(newRule.getCondTerm())) {
                newRules.add(newRule);
                if (digraph != null) {

                    digraph.addVertex(newRule);
                    for (final IGeneralizedRule r : irswt.getRules()) {
                        if (digraph.isEvaluated(otherRule, r) && !digraph.isConnected(otherRule, r)) {
                            digraph.disconnect(newRule, r);
                        }
                        if (digraph.isEvaluated(r, pickedRule) && !digraph.isConnected(r, pickedRule)) {
                            digraph.disconnect(r, newRule);
                        }
                    }
                }
            }
        }
    }

    private IRSwTProblem removeLoopsChaining(
        final Abortion aborter,
        final IRSwTProblem irswt,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph) throws AbortionException
    {
        int maxNumberOfSteps = digraph.getVertices().size();
        boolean changed = false;
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        while (maxNumberOfSteps > 0) {
            IGeneralizedRule pickedRule = null;
            for (final IGeneralizedRule rule : digraph.getVertices()) {
                if (!digraph.isConnected(rule, rule)) {
                    if (digraph.getNeighbors(rule).size() == 1) {
                        pickedRule = rule;
                        break;
                    }
                }
            }

            if (pickedRule == null) {
                break;
            } else {
                final Set<IGeneralizedRule> prevVertices = digraph.getInvertedNeighbors(pickedRule);
                final Set<IGeneralizedRule> nextRules = digraph.getNeighbors(pickedRule);

                assert nextRules.size() == 1 : "Should have size == 1.";
                final IGeneralizedRule nextRule = nextRules.iterator().next();

                final Set<IGeneralizedRule> nextVertices = digraph.getNeighbors(nextRule);

                final Chaining c = new Chaining(pickedRule, nextRule, fng, aborter);
                final IGeneralizedRule result = c.applyChaining();
                if (result != null) {
                    digraph.addVertex(result);
                    for (final IGeneralizedRule otherRule : digraph.getVertices()) {
                        if (otherRule.equals(result) || otherRule.equals(pickedRule) || otherRule.equals(nextRule)) {
                            continue;
                        }
                        if (!prevVertices.contains(otherRule)) {
                            digraph.disconnect(otherRule, result);
                        }
                        if (!nextVertices.contains(otherRule)) {
                            digraph.disconnect(result, otherRule);
                        }
                    }
                    if (!digraph.isConnected(nextRule, pickedRule)) {
                        digraph.disconnect(result, result);
                    }
                    digraph.removeVertex(pickedRule);
                    if (!digraph.isConnected(nextRule, nextRule)) {
                        digraph.removeVertex(nextRule);
                    }
                    digraph.overestimate();
                } else {
                    digraph.disconnect(pickedRule, nextRule);
                }
                changed = true;
            }
            maxNumberOfSteps--;
        }
        if (!changed) {
            return null;
        }
        digraph.freeze();
        return new IRSwTProblem(
            ImmutableCreator.create(new LinkedHashSet<IGeneralizedRule>(digraph.getVertices())),
            digraph);
    }

    /**
     * A truly misbegotten proof!
     * @author Matthias Hoelzel
     */
    class IRSwTChainingProof extends DefaultProof {
        /**
         * Constructor!
         */
        public IRSwTChainingProof() {
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            return eu.tttext("Chaining!");
        }
    }
}
