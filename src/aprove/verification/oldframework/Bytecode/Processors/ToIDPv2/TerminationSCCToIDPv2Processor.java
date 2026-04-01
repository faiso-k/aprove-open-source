package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.GraphProcessors.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This processor takes a TerminationGraph SCC and translates it to an IDP
 * problem by converting each edge of the SCC to a rewrite rule.
 */
public class TerminationSCCToIDPv2Processor extends Processor.ProcessorSkeleton {
    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments extends TerminationSCCToIDPv1Processor.Arguments {
        /**
         * Switches on the internal cleaning procedure (usually used for IDPv1)
         */
        public boolean cleanRules = false;
    }

    /**
     * Parameters for this processor.
     */
    private final Arguments arguments;

    /**
     * Create a fresh processor to transform a FIGraph into an ITRS
     * @param args object holding parameters for this processor
     */
    @ParamsViaArgumentObject
    public TerminationSCCToIDPv2Processor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * @return true for a TerminationGraphProblem.
     * @param obl some obligation that should be a TerminationGraphProblem
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof JBCTerminationSCCProblem;
    }

    /**
     * Work on the given obligation.
     * @param obl a TerminationGraphProblem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return one ITRS for each SCC in the TerminationGraph
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        if (!(obl instanceof JBCTerminationSCCProblem)) {
            assert (false);
            return ResultFactory.unsuccessful();
        }

        // Get rule sets from the graph and turn them into problems.
        final JBCTerminationSCCProblem terminationSCCProblem = (JBCTerminationSCCProblem) obl;

        /*
         * Start workers to create the rule sets for every needed method
         * graph. Needed means that the method is either part of a SCC
         * or called from a SCC.
         */
        final Collection<ToRuleSetConverter> conversionWorkers = new LinkedHashSet<ToRuleSetConverter>();

        final JBCGraph sccSubGraph = terminationSCCProblem.getSCC();
        final SCCAnnotations sccAnnotations = terminationSCCProblem.getSCCAnnotations();

        //Initialize the rule creator and transformation dispatcher:
        final PolyFactory polyFactory = new SharingPolyFactory();
        final ItpfFactory itpfFactory = new SharingItpfFactory(polyFactory);
        final TransformationDispatcher dispatcher = new TransformationDispatcher(sccAnnotations, this.arguments);
        final RuleCreator ruleCreator =
            new RuleCreator(
                terminationSCCProblem.getFullGraph(),
                this.arguments,
                dispatcher,
                sccAnnotations,
                itpfFactory,
                aborter);

        // Create a worker for the SCC:
        final SCCToRuleSetConverter conv = new SCCToRuleSetConverter(aborter, sccSubGraph, ruleCreator);
        conversionWorkers.add(conv);
        PrioritizableThreadPool.INSTANCE.execute(conv);

        // Create a worker for the edges connecting graphs:
        final Set<Edge> connectingEdges = terminationSCCProblem.getOutgoingCallEdges();
        final EdgeSetToRuleSetConverter connecterConv =
            new EdgeSetToRuleSetConverter(aborter, connectingEdges, ruleCreator);
        conversionWorkers.add(connecterConv);
        PrioritizableThreadPool.INSTANCE.execute(connecterConv);

        // Create a worker for the called methods:
        for (final MethodGraph calledGraph : terminationSCCProblem.getHelperGraphs()) {
            final MethodGraphToRuleSetConverter helperConv =
                new MethodGraphToRuleSetConverter(aborter, calledGraph, ruleCreator);
            conversionWorkers.add(helperConv);
            PrioritizableThreadPool.INSTANCE.execute(helperConv);
        }

        Collection<IRule> infRules = new LinkedHashSet<IRule>();
        Collection<IRule> nonInfRules = new LinkedHashSet<IRule>();

        //Now fetch the rule sets and construct the IDP problem:
        for (final ToRuleSetConverter entry : conversionWorkers) {
            try {
                PrioritizableThreadPool.INSTANCE.release();
                entry.waitForConversion();
                PrioritizableThreadPool.INSTANCE.acquire();
                if (entry instanceof SCCToRuleSetConverter) {
                    infRules.addAll(entry.getResult());
                } else {
                    nonInfRules.addAll(entry.getResult());
                }
            } catch (final InterruptedException e) {
                return ResultFactory.unsuccessful("aborted");
            }
        }

        //Some rules appear twice, remove the non-INF variant:
        nonInfRules.removeAll(infRules);

        if (this.arguments.cleanRules) {
            final List<Pair<String, ? extends RuleSet>> conversionLog = new LinkedList<>();

            final Set<IGeneralizedRule> pIGRules = new LinkedHashSet<>();
            for (final IRule infRule : infRules) {
                pIGRules.add(IDPv2ToIDPv1Utilities.ruleToIDPv1(infRule));
            }
            final Set<IGeneralizedRule> rIGRules = new LinkedHashSet<>();
            for (final IRule infRule : nonInfRules) {
                rIGRules.add(IDPv2ToIDPv1Utilities.ruleToIDPv1(infRule));
            }
            final Pair<Set<GeneralizedRule>, Set<GeneralizedRule>> p =
                TerminationSCCToIDPv1Processor.doRuleCleaning(
                    pIGRules,
                    rIGRules,
                    aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap.DEFAULT_MAP,
                    this.arguments,
                    conversionLog,
                    rti,
                    obl.getId(),
                    aborter);

            infRules =
                TerminationSCCToIDPv2Processor.toIRules(TerminationSCCToIDPv1Processor.readdConditions(p.x), itpfFactory, IDPPredefinedMap.DEFAULT_MAP);
            nonInfRules =
                TerminationSCCToIDPv2Processor.toIRules(TerminationSCCToIDPv1Processor.readdConditions(p.y), itpfFactory, IDPPredefinedMap.DEFAULT_MAP);
        }

        final InitialGraphGenerator initialGraphGenerator = new InitialGraphGenerator();
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;

        IDependencyGraph initialGraph;

        try {
            final IQTermSet q = IQTermSet.createConstructorQ(nonInfRules, predefinedMap);
            initialGraph =
                initialGraphGenerator.createInitialGraph(
                    itpfFactory,
                    predefinedMap,
                    infRules,
                    nonInfRules,
                    true,
                    q,
                    aborter);
        } catch (final AbortionException e) {
            return ResultFactory.unsuccessful("aborted");
        }

        //Direct export to QDP if we don't have no predefined symbols:
        if (this.arguments.tryQDPExport && !initialGraph.hasPredefinedDefSymbols()) {
            //May fail to free variables:
            try {
                final Set<IGeneralizedRule> pIGRules = new LinkedHashSet<IGeneralizedRule>();
                for (final IRule infRule : infRules) {
                    pIGRules.add(IDPv2ToIDPv1Utilities.ruleToIDPv1(infRule));
                }
                final Set<IGeneralizedRule> rIGRules = new LinkedHashSet<IGeneralizedRule>();
                for (final IRule infRule : nonInfRules) {
                    rIGRules.add(IDPv2ToIDPv1Utilities.ruleToIDPv1(infRule));
                }

                final ImmutableSet<Rule> pRules =
                    TerminationSCCToIDPv2Processor.convertGeneralizedRulestoRules(IGeneralizedRule.removeConditions(pIGRules));
                final ImmutableSet<Rule> rRules =
                    TerminationSCCToIDPv2Processor.convertGeneralizedRulestoRules(IGeneralizedRule.removeConditions(rIGRules));

                final QTermSet qSet =
                    new QTermSet(aprove.verification.dpframework.BasicStructures.CollectionUtils.getLeftHandSides(rRules));

                final QDPProblem qdp = QDPProblem.create(pRules, QTRSProblem.create(rRules, qSet), true);

                return ResultFactory.proved(
                    qdp,
                    YNMImplication.SOUND,
                    new TerminationSCCToQDPProof(Collections.<Pair<String, ? extends RuleSet>>emptyList()));
            } catch (final AssertionError err) {
                //This was a free var. Ignore.
            }
        }

        return ResultFactory.proved(
            TIDPProblem.create(initialGraph, TerminationSCCToIDPv2Processor.getInfEdges(initialGraph), true),
            YNMImplication.SOUND,
            new TerminationSCCToIDPv2Proof());
    }

    private static ImmutableSet<Rule> convertGeneralizedRulestoRules(final Collection<GeneralizedRule> rules) {
        final LinkedHashSet<Rule> res = new LinkedHashSet<Rule>();
        for (final GeneralizedRule r : rules) {
            res.add(Rule.create(r.getLeft(), r.getRight()));
        }
        return ImmutableCreator.create(res);
    }

    /**
     * @param graph some IDP graph
     * @return set of INF rules in <code>graph</code>
     */
    private static ImmutableSet<IDPSubGraph> getInfEdges(final IDependencyGraph graph) {
        final Set<IEdge> result = new LinkedHashSet<IEdge>();

        for (final IEdge edge : graph.getEdges()) {
            if (edge.type.isInf()) {
                result.add(edge);
            }
        }

        return ImmutableCreator.create(Collections.singleton(new IDPSubGraph(ImmutableCreator.create(result))));
    }

    public static Collection<IRule> toIRules(
        final Collection<IGeneralizedRule> rules,
        final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap)
    {
        final Set<IRule> newRules = new LinkedHashSet<IRule>();
        for (final IGeneralizedRule rule : rules) {
            newRules.add(TerminationSCCToIDPv2Processor.toIRule(rule, itpfFactory, predefinedMap));
        }
        return newRules;
    }

    public static IRule toIRule(
        final IGeneralizedRule rule,
        final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap)
    {
        final TRSFunctionApplication oldL = rule.getLeft();
        final TRSTerm oldR = rule.getRight();
        final TRSTerm oldCond = rule.getCondTerm();

        final IFunctionApplication<?> newL = (IFunctionApplication<?>) IDPPredefinedMap.toITerm(oldL, predefinedMap);
        final ITerm<?> newR = IDPPredefinedMap.toITerm(oldR, predefinedMap);

        if (oldCond != null) {
            final ITerm<BooleanRing> newCond = (ITerm<BooleanRing>) IDPPredefinedMap.toITerm(oldCond, predefinedMap);
            return IRuleFactory.createWithExQuantifiedFreeVars(newL, newR, newCond, predefinedMap, itpfFactory, true);
        } else {
            return IRuleFactory.create(newL, newR);
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    public class TerminationSCCToIDPv2Proof extends DefaultProof {
        /**
         * Create the proof.
         */
        public TerminationSCCToIDPv2Proof() {
            super();
            this.shortName = "SCCToIDPv2Proof";
            this.longName = "TerminationSCCToIDPv2Proof";
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed TerminationGraph SCC to IDP.";
        }
    }

    /**
     * A very fine proof.
     * @author brockschmidt (don't blame me)
     */
    public static class TerminationSCCToQDPProof extends DefaultProof {
        /**
         * Some documentation about the magic we've done.
         */
        private final List<Pair<String, ? extends RuleSet>> log;

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public TerminationSCCToQDPProof(final List<Pair<String, ? extends RuleSet>> l) {
            super();
            this.log = l;
            this.shortName = "SCCToQDPProof";
            this.longName = "TerminationSCCToQDPProof";
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Transformed TerminationGraph SCC to QDP. Log: ");
            sb.append(o.linebreak());
            for (final Pair<String, ? extends RuleSet> entry : this.log) {
                sb.append(o.indent(entry.x));
                if (entry.y != null) {
                    sb.append(o.indent(entry.y.export(o)));
                } else {
                    sb.append(o.linebreak());
                }
            }
            return sb.toString();
        }
    }
}
