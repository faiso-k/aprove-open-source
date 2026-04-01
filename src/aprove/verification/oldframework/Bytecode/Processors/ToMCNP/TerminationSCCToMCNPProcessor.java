package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Bytecode.Processors.PathLength.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * This processor takes a TerminationGraph SCC and translates it to a MCNP
 * problem by converting each edge of the SCC to a ITRS rewrite rule,
 * simplifying these and then converting everything to MCNP.
 *
 * @author Christian von Essen, Matthias Hoelzel, Marc Brockschmidt
 */
public class TerminationSCCToMCNPProcessor extends Processor.ProcessorSkeleton {
    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments extends ConverterArguments {
        /**
         * Use path length encoding. If it's not used, all object encoding
         * will be filtered away.
         */
        public boolean usePathLength = true;
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
    public TerminationSCCToMCNPProcessor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * @return true for a JBCTerminationSCCProblem.
     * @param obl some obligation that should be a JBCTerminationSCCProblem
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof JBCTerminationSCCProblem;
    }

    /**
     * Work on the given obligation.
     * @param obl an FI Graph
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return one MCNP for each SCC in the FI Graph
     */
    @Override
    public Result process(final BasicObligation obl,
            final BasicObligationNode oblNode, final Abortion aborter,
            final RuntimeInformation rti) throws AbortionException {
        if (!(obl instanceof JBCTerminationSCCProblem)) {
            assert (false);
            return ResultFactory.unsuccessful();
        }
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        final List<Pair<String, RuleSet>> conversionLog = new LinkedList<>();

        // Get rule sets from the graph and turn them into problems.
        final JBCTerminationSCCProblem terminationSCCProblem = (JBCTerminationSCCProblem) obl;

        // Edges from the SCC shall be converted into rules in P. We can
        // ignore R here.
        final Collection<Edge> pEdges = terminationSCCProblem.getSCC().getEdges();

        //Initialize the rule creator and transformation dispatcher:
        final PolyFactory polyFactory = new SharingPolyFactory();
        final ItpfFactory itpfFactory = new SharingItpfFactory(polyFactory);
        final SCCAnnotations sccAnnotations =
            terminationSCCProblem.getSCCAnnotations();
        final TransformationDispatcher dispatcher =
            new TransformationDispatcher(sccAnnotations, this.arguments);
        final RuleCreator ruleCreator =
            new RuleCreator(terminationSCCProblem.getFullGraph(), this.arguments, dispatcher, sccAnnotations,
                itpfFactory, aborter);

        Set<IGeneralizedRule> iGRules = IDPv2ToIDPv1Utilities.convertEdgesToIDPv1(
                aborter, ruleCreator, false, sccAnnotations, dispatcher, pEdges, true);

        conversionLog.add(new Pair<String, RuleSet>(
                "Generated rules. Obtained " + iGRules.size() + " IRules",
                new IGeneralizedRuleSet(iGRules, null)));

        RuleCombiner combiner = new RuleCombiner(iGRules, Collections.emptySet(), aborter);
        iGRules = combiner.combineRules(false, true).y;

        conversionLog.add(new Pair<String, RuleSet>(
                "Combined rules. Obtained " + iGRules.size() + " IRules",
                new IGeneralizedRuleSet(iGRules, null)));

        // Transform constraints
        Set<GeneralizedRule> gRules = IGeneralizedRule.removeConditions(iGRules, true);
        Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
               Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
               Collection<Rule>> resultTriple;

        final GroundTermRemover groundTermRemover = new GroundTermRemover();
        final DuplicateArgsRemover duplicateArgsRemover = new DuplicateArgsRemover();
        final UnneededArgumentRemover unneededArgumentRemover = new UnneededArgumentRemover();

        resultTriple = groundTermRemover.processRulePair(gRules, Collections.<GeneralizedRule>emptySet(), predefinedMap);
        if (resultTriple != null) {
            gRules = resultTriple.x.x;
            conversionLog.add(new Pair<>("Filtered ground terms:", new RuleSet(resultTriple.z)));
        }

        resultTriple = duplicateArgsRemover.processRulePair(gRules, Collections.<GeneralizedRule>emptySet(), predefinedMap);
        if (resultTriple != null) {
            gRules = resultTriple.x.x;
            conversionLog.add(new Pair<>("Filtered duplicate terms:", new RuleSet(resultTriple.z)));
        }

        resultTriple = unneededArgumentRemover.processRulePair(gRules, Collections.<GeneralizedRule>emptySet(), predefinedMap);
        if (resultTriple != null) {
            gRules = resultTriple.x.x;
            conversionLog.add(new Pair<>("Filtered unneeded terms:", new RuleSet(resultTriple.z)));
        }

        if (this.arguments.usePathLength) {
            gRules = PathLength.translateRuleSet(gRules, predefinedMap);
        } else {
            final ObjectTermRemover objectArgumentRemover = new ObjectTermRemover();
            resultTriple =
                objectArgumentRemover.processRulePair(gRules, Collections.<GeneralizedRule>emptySet(), predefinedMap);
            if (resultTriple != null) {
                gRules = resultTriple.x.x;
                conversionLog.add(new Pair<>("Filtered all non-integer terms:", new RuleSet(resultTriple.z)));
            }
        }

        iGRules = TerminationSCCToIDPv1Processor.readdConditions(gRules);
        iGRules = TerminationSCCToIDPv1Processor.cleanConstraints(iGRules, false, false, predefinedMap, aborter);
        iGRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(iGRules, predefinedMap);
        combiner = new RuleCombiner(iGRules, Collections.emptySet(), aborter);
        iGRules = combiner.combineRules(false, true).y;
        iGRules = TerminationSCCToIDPv1Processor.cleanConstraints(iGRules, true, false, predefinedMap, aborter);
        iGRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(iGRules, predefinedMap);

        conversionLog.add(new Pair<String, RuleSet>(
                "Finished conversion. Obtained " + iGRules.size() + " rules.",
                new IGeneralizedRuleSet(iGRules, null)));

        gRules = IGeneralizedRule.removeConditions(iGRules, true);

        final Collection<TRSFunctionApplication> lhs = new LinkedList<>();
        for (final GeneralizedRule rule : gRules) {
            lhs.add(rule.getLeft());
        }
        return ResultFactory.proved(ITRSProblem.create(gRules,
 new IQTermSet(new QTermSet(lhs), predefinedMap)),
                YNMImplication.SOUND, new TerminationSCCToMCNPProof(conversionLog));
    }


    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    public class TerminationSCCToMCNPProof extends DefaultProof {
        /**
         * Some documentation about the magic we've done.
         */
        private final List<Pair<String, RuleSet>> log;

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public TerminationSCCToMCNPProof(
                final List<Pair<String, RuleSet>> l) {
            super();
            this.log = l;
            this.shortName = "SCCToMCNPProof";
            this.longName = "TerminationSCCToMCNPProof";
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Transformed FIGraph SCCs to MCNP. Log: ");
            sb.append(o.linebreak());
            for (final Pair<String, RuleSet> entry : this.log) {
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
