package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Converts a given graph into a set of IRSwT-Rules according to the
 * transformation detailed in A. Weinert's Master Thesis
 *
 * @author Alexander Weinert
 */
class GraphToIRSwTConverter {
    private final Abortion aborter;

    /**
     * An adaptor around a {@link PrologEvaluationGraph} that allows us to
     * easily access the nodes and paths that are of interest for transformation
     * into an IRSwT
     */
    private final GraphAnalyzer analyzer;

    /**
     * By default, the actual computation is delegated to an instance of
     * GraphAnalyzer and RuleFactory, respectively, which each get a reference
     * to the given aborter. Also, a new fresh name generator is instantiated to
     * construct variable names.
     *
     * @param aborter Some aborter. Must not be null.
     * @return A new default GraphToIRSwTConverter. Is never null.
     */
    static GraphToIRSwTConverter create(Abortion aborter) {
        return new GraphToIRSwTConverter(new GraphAnalyzer(), aborter);
    }

    GraphToIRSwTConverter(GraphAnalyzer analyzer, Abortion aborter) {
        this.analyzer = analyzer;
        this.aborter = aborter;
    }

    /**
     * The encoding of a PrologEvaluationGraph into a set of IRSwT is detailed
     * in A. Weinert's Master Thesis. The idea is that all executions described
     * by the given graph are terminating if all of the IRSwTProblems returned
     * by this method are terminating
     *
     * @param graph
     *            Some fully expanded PrologEvaluationGraph. Must not be null.
     * @return The encoding of the given graph as a set of IRSwT problems. Is
     *         never null.
     */
    Collection<IRSwTProblem> convert(PrologEvaluationGraph graph) {
        final Collection<IRSwTProblem> returnValue = new LinkedList<>();

        for(Cycle<PrologAbstractState> scc : graph.getSCCs(true)) {
            final Collection<Node<PrologAbstractState>> nodesToEncode = this.computeNodesToEncode(graph, scc);
            final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
            final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.PROLOG_FUNCS);
            final NodeEncoder encoder = new NodeEncoder(graph, AbstractGraphBuilderHeuristic.generateGroundnessAnalysis(graph), fng, this.aborter);

            for(Node<PrologAbstractState> node : nodesToEncode) {
                rules.addAll(encoder.encodeNode(node));
            }
            rules.addAll(encoder.encodePathsToCycle(scc));

            returnValue.add(new IRSwTProblem(ImmutableCreator.create(rules), encoder.encodeRootIn()));
        }

        return returnValue;
    }

    private Collection<Node<PrologAbstractState>> computeNodesToEncode(
            PrologEvaluationGraph graph, Cycle<PrologAbstractState> scc) {
        final Collection<Node<PrologAbstractState>> returnValue = new HashSet<>(scc);
        for(Node<PrologAbstractState> node : scc) {
            if(graph.isSplitNode(node)) {
                for(Node<PrologAbstractState> succ : graph.getOut(node)) {
                    if(!scc.contains(succ)) {
                        returnValue.addAll(graph.determineReachableNodes(Collections.singleton(succ)));
                    }
                }
            }
        }
        return returnValue;
    }
}