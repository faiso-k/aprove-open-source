package aprove.verification.oldframework.Bytecode.Processors.ToComplexity;

import static aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.JBCGraph.*;
import static aprove.verification.oldframework.Input.HandlingMode.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

import java.math.*;
import java.util.*;
import java.util.function.*;
import java.util.logging.*;

import org.stringtemplate.v4.compiler.CodeGenerator.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor takes a TerminationGraph and returns a set of edges needed for measuring complexity.
 */
public class TerminationGraphToComplexityRuleSetProcessor extends Processor.ProcessorSkeleton {
    /**
     * Logger needed for output when any of the fancy reflection stuff fails:
     */
    private static final Logger LOGGER = Logger.getLogger("SCCAnnotations");

    /**
     * List of SCC analysis processors that should be used.
     */
    private final List<Class<? extends SCCAnalysis>> sccAnalyses;

    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments {
        /**
         * Space-separated list of SCC analysis processors that should be used.
         */
        public String applyAnalyses = "";
        public ComplexityGoalTerm goalTerm;
        public boolean keepLeaves = false;
        public Optional<HandlingMode> goal = Optional.empty();

        public void setGoalTermFromString(String s) {
            this.goalTerm = ComplexityGoalTerm.fromString(s).get();
        }

        public void setGoal(HandlingMode m) {
            this.goal = Optional.of(m);
        }
    }

    /**
     * Parameters for this processor.
     */
    private final Arguments arguments;

    /**
     * Create a fresh processor to transform a TerminationGraph into an IDP
     * @param args object holding parameters for this processor
     */
    @SuppressWarnings("unchecked")
    @ParamsViaArgumentObject
    public TerminationGraphToComplexityRuleSetProcessor(final Arguments args) {
        this.arguments = args;
        this.sccAnalyses = new LinkedList<>();
        if (this.arguments.applyAnalyses != null && this.arguments.applyAnalyses.length() > 0) {
            for (final String analysisProcName : this.arguments.applyAnalyses.split(" +")) {
                try {
                    final Class<? extends SCCAnalysis> analysisProcClass =
                        (Class<? extends SCCAnalysis>) Class.forName(analysisProcName);
                    this.sccAnalyses.add(analysisProcClass);
                } catch (final ClassNotFoundException e) {
                    //Inform user, run away:
                    LOGGER.log(
                        Level.SEVERE,
                        "Could not find SCC analysis processor " + analysisProcName + ": " + e.getMessage());
                }
            }
        }
    }

    /**
     * @return true for a TerminationGraphProblem.
     * @param obl some obligation that should be a TerminationGraphProblem
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof JBCTerminationGraphProblem;
    }

    /**
     * Work on the given obligation.
     * @param obl a TerminationGraphProblem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return one obligation per SCC
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        if (!(obl instanceof JBCTerminationGraphProblem)) {
            assert (false);
            return ResultFactory.unsuccessful();
        }
        JBCTerminationGraphProblem termGraphProblem = (JBCTerminationGraphProblem) obl;
        HandlingMode goal = arguments.goal.orElse(termGraphProblem.getGraph().getGoal());
        return processInternal(termGraphProblem, goal, arguments.goalTerm);
    }

    protected Result processInternal(JBCTerminationGraphProblem terminationGraphProblem, HandlingMode goal, ComplexityGoalTerm goalTerm) {
        TerminationGraph terminationGraph = terminationGraphProblem.getGraph();
        // Get rule sets from the graph and turn them into problems.
        terminationGraph.dumpImage(false);

        /*
         * Merge method graphs into one graph, make call/return edges
         * explicit. We then search for the SCCs and encode these as
         * separate problems to IDP. For each node, note in which method
         * graph it is.
         */
        final Map<Node, MethodGraph> nodeToMethodGraphMap = new LinkedHashMap<>();
        final Map<Node, Node> oldNodeToNewNodeMap = new LinkedHashMap<>();

        final JBCGraph termGraph =
            TerminationGraphToSingleGraph
                .createSingleGraph(terminationGraph, nodeToMethodGraphMap, oldNodeToNewNodeMap);

        final Pair<Set<Edge>, BigInteger> p = computeEdges(goal, termGraph);
        Set<Edge> edges = p.x;
        BigInteger costs = p.y;

        if (edges.isEmpty()) {
            onEdgesEmpty(terminationGraphProblem);
            ComplexityValue res = ComplexityValue.constant().withConcreteValue(MinMaxExpr.createInt(costs));
            return ResultFactory.provedWithValue(ComplexityYNM.createUpper(res), new TerminationGraphToComplexityProof(0, goal));
        } else {
            //Get start node (in new graph):
            final Node startNode = oldNodeToNewNodeMap.get(terminationGraph.getStartGraph().getStartNode());
            final SCCAnnotations sccAnnotations = new SCCAnnotations(getSubGraphByEdges(edges));
            for (final Class<? extends SCCAnalysis> analysis : this.sccAnalyses) {
                sccAnnotations.doAnalysis(analysis);
            }
            JBCGraphEdgesComplexityProblem newObl = getNewObligation(termGraph, startNode, edges, sccAnnotations, terminationGraphProblem);
            newObl.setGoal(goal, Optional.ofNullable(goalTerm));
            return ResultFactory.proved(
                    newObl,
                    BothBounds.forConcreteBounds(IdentityComputation.create(), new SumComputation(ComplexityValue.constant(costs))),
                    new TerminationGraphToComplexityProof(edges.size(), goal));
        }
    }

    protected void onEdgesEmpty(JBCTerminationGraphProblem obl) {}
    protected JBCGraphEdgesComplexityProblem getNewObligation(JBCGraph termGraph, Node startNode, Set<Edge> edges, SCCAnnotations sccAnnotations, JBCTerminationGraphProblem obl) {
        if (arguments.keepLeaves) {
            return JBCGraphEdgesComplexityProblem.createCESExportable(termGraph, startNode, edges, sccAnnotations, obl.getRelevanceInfo());
        } else {
            return JBCGraphEdgesComplexityProblem.create(termGraph, startNode, edges, sccAnnotations, obl.getRelevanceInfo());
        }
    }

    private Pair<Set<Edge>, BigInteger> computeEdges(HandlingMode goal, final JBCGraph termGraph) {
        // This will hold the result:
        final Set<Edge> edges = new LinkedHashSet<>(termGraph.getEdges());
        BigInteger costs = BigInteger.ZERO;
        if (goal == SpaceComplexity) {
            filterEdgesForSpaceAnalysis(termGraph, edges);
        }
        if (arguments.keepLeaves) {
            return new Pair<>(edges, costs);
        }
        // Maps each node to its outdegree
        Map<Node, Long> out = new DefaultValueMap<>(0l);
        Function<Node, Long> outDegree = n -> edges.stream().filter(e -> e.getStart().equals(n)).count();
        out.putAll(termGraph.getNodes().stream().collect(toMap(x -> x, outDegree)));
        // Remove edges with constant costs where the endnode has outdegree 0 iteratively
        Set<Set<Node>> sccs = termGraph.getSCCs();
        boolean changed;
        do {
            // remove edges to leaves with constant costs
            changed = false;
            Iterator<Edge> it = edges.iterator();
            while (it.hasNext()) {
                Edge edge = it.next();
                BigInteger constantCosts = getConstantCosts(edge, goal);
                if (out.get(edge.getEnd()) == 0 && constantCosts != null) {
                    costs = costs.add(constantCosts);
                    it.remove();
                    changed = true;
                    out.put(edge.getStart(), out.get(edge.getStart()) - 1);
                }
            }
            Set<Node> nodes = new LinkedHashSet<>();
            for (Edge e: edges) {
                nodes.add(e.getStart());
                nodes.add(e.getEnd());
            }
            // remove SCCs with cost 0 without successors
            Iterator<Set<Node>> sccIt = sccs.iterator();
            OUTER: while (sccIt.hasNext()) {
                Set<Node> scc = sccIt.next();
                Set<Edge> toRemove = new LinkedHashSet<>();
                for (Node n: scc) {
                    Set<Edge> nEdges = n.getOutEdges();
                    Set<Node> succs = new LinkedHashSet<>();
                    for (Edge e: nEdges) {
                        if (!BigInteger.ZERO.equals(getConstantCosts(e, goal))) {
                            // keep SCCs with edges with non-zero costs
                            continue OUTER;
                        }
                        succs.add(e.getEnd());
                        toRemove.add(e);
                    }
                    succs.removeAll(scc);
                    if (succs.removeAll(nodes)) {
                        // keep SCCs with edges that lead out of the SCC
                        continue OUTER;
                    }
                }
                sccIt.remove();
                for (Edge e: toRemove) {
                    boolean removed = edges.remove(e);
                    changed |= removed;
                    if (removed) {
                        out.put(e.getStart(), out.get(e.getStart()) - 1);
                    }
                }
            }
        } while (changed);
        return new Pair<>(edges, costs);
    }

    private void filterEdgesForSpaceAnalysis(JBCGraph termGraph, Set<Edge> edges) {
        Set<Set<Node>> nodeSccs = termGraph.getSCCs();
        Function<Set<Node>, Set<Edge>> nodeSCCToEdgeSCC = scc -> scc.stream().flatMap(n -> n.getOutEdges().stream().filter(e -> scc.contains(e.getEnd()))).collect(toSet());
        Set<Set<Edge>> sccs = nodeSccs.stream().map(nodeSCCToEdgeSCC).collect(toSet());
        Set<Set<Edge>> nonZeroCostSCCs = sccs.stream().filter(scc -> scc.stream().anyMatch(e -> !BigInteger.ZERO.equals(getConstantCosts(e, SpaceComplexity)))).collect(toSet());
        Set<Set<Edge>> zeroCostSCCs = difference(sccs, nonZeroCostSCCs);
        Set<Edge> sccEdges = sccs.stream().flatMap(x -> x.stream()).collect(toSet());
        Set<Edge> nonSCCEdges = difference(edges, sccEdges);
        Set<Edge> nonNegligibleNonSCCEdges = nonSCCEdges.stream().filter(e -> getConstantCosts(e, SpaceComplexity) == null).collect(toSet());
        Set<Edge> nonZeroCostSCCRepresentatives = nonZeroCostSCCs.stream().map(scc -> scc.iterator().next()).collect(toSet());
        Set<Edge> negligibleRepresentatives = union(nonNegligibleNonSCCEdges, nonZeroCostSCCRepresentatives);
        for (Set<Edge> scc: zeroCostSCCs) {
            Node representative = scc.iterator().next().getStart();
            if (negligibleRepresentatives.stream().allMatch(e -> !hasPath(representative, e.getStart(), false, null))) {
                edges.removeAll(scc);
            }
        }
    }

    private static BigInteger getConstantCosts(Edge edge, HandlingMode goal) {
        if (edge.getLabel() instanceof PredefinedMethodEdge) {
            PredefinedMethodEdge pme = (PredefinedMethodEdge) edge.getLabel();
            switch (goal) {
            case RuntimeComplexity:
            case UserDefined:
                if (pme.getUpperTimeBound().isConstant()) {
                    return pme.getUpperTimeBound().getConstantSize();
                } else {
                    return null;
                }
            case SpaceComplexity:
                if (pme.getUpperSpaceBound().isConstant()) {
                    return pme.getUpperSpaceBound().getConstantSize();
                } else {
                    return null;
                }
            case SizeComplexity:
                if (!edge.getEnd().getState().callStackEmpty()) {
                    return BigInteger.ZERO;
                } else {
                    return null;
                }
            default:
                throw new RuntimeException(goal + " not supported for JBC");
            }
        } else if (edge.getLabel() instanceof CallAbstractEdge) {
            return null;
        } else if (edge.getLabel() instanceof MethodSkipEdge) {
            return null;
        } else if (edge.getLabel() instanceof EvaluationEdge) {
            switch (goal) {
            case RuntimeComplexity:
                return BigInteger.ONE;
            case UserDefined:
                return BigInteger.ZERO;
            case SpaceComplexity:
                State start = edge.getStart().getState();
                OpCode oc = start.getCurrentOpCode();
                if (oc instanceof ArrayCreate) {
                    State end = edge.getEnd().getState();
                    if (start.getCurrentStackFrame().hasException() || (end.getCurrentStackFrame() != null && end.getCurrentStackFrame().hasException())) {
                        return BigInteger.ZERO;
                    }
                    ArrayCreate ac = (ArrayCreate) oc;
                    int dimension = ac.getNumberOfArguments();
                    OperandStack opStack = start.getCurrentStackFrame().getOperandStack().clone();
                    BigInteger size = BigInteger.ONE;
                    for (int i = 0; i < dimension; i++) {
                        AbstractVariableReference lengthArg = opStack.pop();
                        if (!lengthArg.pointsToConstantInt()) {
                            return null;
                        } else {
                            size = size.multiply(((LiteralInt) start.getAbstractVariable(lengthArg)).getIntLiteralValue());
                        }
                    }
                    return size;
                } else if (oc instanceof New) {
                    return BigInteger.ONE;
                }
                return BigInteger.ZERO;
            case SizeComplexity:
                if (!edge.getEnd().getState().callStackEmpty()) {
                    return BigInteger.ZERO;
                } else {
                    return null;
                }
            default:
                throw new RuntimeException(goal + " not supported for JBC");
            }
        }
        return BigInteger.ZERO;
    }

    /**
     * A very fine proof.
     * @author Marc Brockschmidt
     */
    public class TerminationGraphToComplexityProof extends DefaultProof {
        private final int numRules;
        private final HandlingMode goal;

        public TerminationGraphToComplexityProof(int numRules, HandlingMode goal) {
            this.numRules = numRules;
            this.goal = goal;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            if (this.numRules == 0) {
                return "Proven constant complexity by absence of SCCs and edges with non-constant weight";
            } else {
                String res = "Extracted set of " + numRules + " edge" + (numRules > 1 ? "s" : "") + " for the analysis of " + goal + ".";
                if (arguments.keepLeaves) {
                    res += " Kept leaves.";
                } else {
                    res += " Dropped leaves.";
                }
                return res;
            }
        }
    }
}
