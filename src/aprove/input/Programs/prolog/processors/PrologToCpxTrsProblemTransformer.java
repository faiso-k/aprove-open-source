package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * The PrologToCpxTrsProblemTransformer builds a termination graph
 * and extracts CpxTrsProblems from these for which an upper bound
 * guarantees this upper bound for the PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */

public class PrologToCpxTrsProblemTransformer extends PrologGraphProcessor {

    /**
     * @author cryingshadow
     *
     */
    public class PrologToCpxTrsProblemTransformerProof extends PrologGraphProcessorProof {

        /**
         * @param petGraph
         * @param exportGraph
         * @param exportLimit
         * @param nodeLabels
         */
        public PrologToCpxTrsProblemTransformerProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit,
            final Map<Integer, String> nodeLabels)
        {
            super(petGraph, exportGraph, exportLimit, nodeLabels);
        }

        @Override
        protected String getProofMessage() {
            //TODO add citation
            return "Built complexity preserving TRS problem from derivation graph.";
        }

    }

    /**
     * The standard logger.
     */
    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToCpxTrsProblemTransformer");

    /**
     * Standard constructor.
     * @param args The arguments.
     */
    @ParamsViaArgumentObject
    public PrologToCpxTrsProblemTransformer(final PrologOptions args) {
        super(args);
        this.options.setComplexityHeuristic(true);
    }

    /**
     * @param graph
     * @param nodeLabels
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public static RuntimeComplexityTrsProblem calculateCpxTrsProblemFromGraph(
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        final CpxNodeSets cpxSet = graph.getCpxNodeSetsForPaths(aborter);
        //        The following is not necessary as we only consider ground variables in TRSs.
        //        As soon as we lift this restriction, we also need to consider evil PARALLEL nodes!
        //        if (PrologToComplexityProblemTransformer.hasEvilParallel(graph, cpxSet, aborter)) {
        //            return null;
        //        }
        final Set<Node<PrologAbstractState>> multiplicativeSplits =
            PrologToComplexityProblemTransformer.calculateMultiplicativeSplits(graph, cpxSet, aborter);
        aborter.checkAbortion();
        if (!multiplicativeSplits.isEmpty()) {
            return null;
        }
        final Set<String> used = new LinkedHashSet<String>();
        used.add("U");
        used.add("X");
        used.add("f");
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
        final GroundnessAnalysis ground = AbstractGraphBuilderHeuristic.generateGroundnessAnalysis(graph);
        final List<Pair<Node<PrologAbstractState>, CpxNodeSets>> sets =
            new ArrayList<Pair<Node<PrologAbstractState>, CpxNodeSets>>();
        sets.add(new Pair<Node<PrologAbstractState>, CpxNodeSets>(graph.getRoot(), cpxSet));
        final List<Pair<Node<PrologAbstractState>, Set<List<Node<PrologAbstractState>>>>> pathList =
            PrologToComplexityProblemTransformer
                .calculateAllConnectionPaths(graph, sets, multiplicativeSplits, aborter);
        if (Globals.useAssertions) {
            assert (pathList.size() == 1) : "How can we obtain several TRSs if there is no multiplicative SPLIT?";
        }

        final Set<Rule> rules = new LinkedHashSet<Rule>();
        for (final List<Node<PrologAbstractState>> path : pathList.get(0).y) {
            rules.addAll(RuleConstructor.buildConnectionRules(path, graph, ground, fridge, aborter));
        }
        for (final Node<PrologAbstractState> split : cpxSet.getSplitNodes()) {
            rules.addAll(RuleConstructor.buildSplitRules(split, graph, ground, true, fridge, aborter));
        }
        // Rules for PARALLEL nodes are necessary since PARALLEL nodes reaching themselves can lead to exponential
        // runtime!
        for (final Node<PrologAbstractState> parallel : cpxSet.getParallelNodes()) {
            rules.addAll(RuleConstructor.buildParallelRules(parallel, graph, ground, fridge, aborter));
        }
        return RuntimeComplexityTrsProblem.create(ImmutableCreator.create(rules), RewriteStrategy.INNERMOST);
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.COMPLEXITY);
    }

    @Override
    protected Logger getLogger() {
        return PrologToCpxTrsProblemTransformer.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToCpxTrsProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        //        Set<CpxTrsProblem> pps = new LinkedHashSet<CpxTrsProblem>();
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final RuntimeComplexityTrsProblem obligation =
            PrologToCpxTrsProblemTransformer.calculateCpxTrsProblemFromGraph(graph, nodeLabels, aborter);
        if (aborter.isAborted()) {
            return ResultFactory.aborted("problem extraction took too long");
        }
        //        pps.add(problemFromGraph);
        if (PrologToCpxTrsProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToCpxTrsProblemTransformer.log.log(Level.FINE, "Reading CpxTrsProblem: {0}ms\n", time / 1000000);
        }
        if (obligation == null) {
            return ResultFactory.unsuccessful("Constructed graph is no complexity graph!");
        }
        return ResultFactory.proved(obligation, UpperBound.create(), new PrologToCpxTrsProblemTransformerProof(
            graph,
            this.options.isExportTree(),
            this.options.getTreeLimit(),
            nodeLabels));
    }

}
