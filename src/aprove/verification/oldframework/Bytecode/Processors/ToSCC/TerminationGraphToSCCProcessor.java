package aprove.verification.oldframework.Bytecode.Processors.ToSCC;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.Graphs.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This processor takes a TerminationGraph and splits it into SCCs which can
 * be analyzed on their own.
 */
public class TerminationGraphToSCCProcessor extends Processor.ProcessorSkeleton {
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

        /**
         * This disables the split of the analysis into single SCCs, but just encodes the full termination graph. Upside
         * is that the resulting SCC has a start state (namely, the start state of the first termination graph).
         */
        public boolean singleResultSystem = false;
    }

    /**
     * Parameters for this processor.
     */
    private final Arguments arguments;

    /**
     * Create a fresh processor to transform a TerminationGraph into an IDP
     * @param args object holding parameters for this processor
     */
    @ParamsViaArgumentObject
    public TerminationGraphToSCCProcessor(final Arguments args) {
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
                    TerminationGraphToSCCProcessor.LOGGER.log(
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
        return (obl instanceof JBCTerminationGraphProblem);
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

        // Get rule sets from the graph and turn them into problems.
        final JBCTerminationGraphProblem terminationGraphProblem = (JBCTerminationGraphProblem) obl;
        final TerminationGraph terminationGraph = terminationGraphProblem.getGraph();

        final Map<Node, MethodGraph> nodeToMethodGraphMap = new LinkedHashMap<>();
        final Map<Node, Node> oldToNewMap = new LinkedHashMap<>();

        /*
         * Merge method graphs into one graph, make call/return edges
         * explicit. We then search for the SCCs and encode these as
         * separate problems to IDP. For each node, note in which method
         * graph it is.
         */
        final JBCGraph termGraph =
            TerminationGraphToSingleGraph.createSingleGraph(terminationGraph, nodeToMethodGraphMap, oldToNewMap);


        /*
         * Start workers to create the rule sets for every needed method
         * graph. Needed means that the method is either part of a SCC
         * or called from a SCC.
         */
        final LinkedHashSet<Set<Node>> sccs = termGraph.getSCCs(new EdgeTypeFilter(MethodReturnEdge.class));

        final Collection<JBCTerminationSCCProblem> problems = new LinkedHashSet<>();
        for (final Set<Node> scc : sccs) {
            final JBCGraph sccSubGraph = termGraph.getSubGraph(scc);
            final SCCAnnotations sccAnnotations = new SCCAnnotations(sccSubGraph);

            for (final Class<? extends SCCAnalysis> analysis : this.sccAnalyses) {
                sccAnnotations.doAnalysis(analysis);
            }

            final JBCGraph fullGraph = new JBCGraph();

            //find all graphs in the SCC:
            final LinkedHashSet<MethodGraph> sccGraphs = new LinkedHashSet<>();
            for (final Node node : scc) {
                sccGraphs.add(nodeToMethodGraphMap.get(node));
            }

            //find all graphs called from the SCC:
            final Set<Edge> outgoingCallEdges = new LinkedHashSet<>();
            final Set<Edge> incomingReturnEdges = new LinkedHashSet<>();
            final Set<MethodGraph> toCheckGraphs = new LinkedHashSet<>();
            for (final Node node : scc) {
                for (final Edge outEdge : node.getOutEdges()) {
                    final Node targetNode = outEdge.getEnd();
                    if (scc.contains(targetNode)) {
                        fullGraph.createCopiedEdge(outEdge);
                    }

                    //If this is a call edge which leads to something which
                    //is not in the SCC, encode it:
                    final EdgeInformation label = outEdge.getLabel();
                    if (label instanceof CallAbstractEdge) {
                        sccSubGraph.createCopiedEdge(outEdge);
                        if (!scc.contains(targetNode)) {
                            fullGraph.createCopiedEdge(outEdge);
                            outgoingCallEdges.add(outEdge);
                            final LinkedList<Edge> todo = new LinkedList<>();
                            todo.addAll(targetNode.getOutEdges());
                            while (!todo.isEmpty()) {
                                final Edge outOutEdge = todo.pop();
                                fullGraph.createCopiedEdge(outOutEdge);
                                outgoingCallEdges.add(outOutEdge);
                                if (outOutEdge.getLabel() instanceof InstanceEdgeBetweenGraphs) {
                                    final MethodGraph calledGraph = nodeToMethodGraphMap.get(outOutEdge.getEnd());
                                    toCheckGraphs.add(calledGraph);
                                } else {
                                    todo.addAll(outOutEdge.getEnd().getOutEdges());
                                }
                            }
                        } else {
                            /*
                             * We are staying in the same graph, so we should
                             * also encode the non-SCC parts to R:
                             */
                            toCheckGraphs.add(nodeToMethodGraphMap.get(targetNode));
                        }
                    } else if (label instanceof MethodSkipEdge) {
                        final MethodSkipEdge mse = (MethodSkipEdge) label;
                        final Node returnNode = mse.getNode();
                        /*
                         * Sometimes, the corresponding return state was
                         * already deleted. Then, we don't need to check
                         *  this edge.
                         */
                        if (!oldToNewMap.containsKey(returnNode)
                            || !sccSubGraph.containsState(outEdge.getEnd().getState()))
                        {
                            continue;
                        }
                        final Edge returnEdge = new Edge(returnNode, new MethodReturnEdge(), targetNode);
                        fullGraph.createCopiedEdge(returnEdge);
                        incomingReturnEdges.add(returnEdge);
                    }
                }
            }

            /*
             * Check what graphs are called (indirectly) from the SCC and store
             * these connections.
             */
            final Set<MethodGraph> helperGraphs = new LinkedHashSet<>();
            helperGraphs.addAll(toCheckGraphs);
            while (!toCheckGraphs.isEmpty()) {
                final Iterator<MethodGraph> it = toCheckGraphs.iterator();
                final MethodGraph graph = it.next();
                it.remove();

                for (final Edge edge : graph.getEdges()) {
                    if (sccSubGraph.containsState(edge.getStart().getState())
                        && sccSubGraph.containsState(edge.getEnd().getState()))
                    {
                        continue;
                    }
                    fullGraph.createCopiedEdge(edge);

                    //If this edge will lead to another graph, search for the
                    //other graph (we have only successor now!):
                    final EdgeInformation label = edge.getLabel();
                    if (label instanceof CallAbstractEdge) {
                        Node curNode = edge.getEnd();
                        while (!curNode.getOutEdges().isEmpty()) {
                            curNode = curNode.getOutEdges().iterator().next().getEnd();
                        }
                        /*
                         * This is the last state before we switch to another
                         * graph, so switch to the complete graph we constructed
                         * and find the inter-state edge:
                         */
                        final Node curNodeInOtherGraph = oldToNewMap.get(curNode);

                        if (!curNodeInOtherGraph.getOutEdges().isEmpty()) {
                            final Edge callEdge = curNodeInOtherGraph.getOutEdges().iterator().next();

                            outgoingCallEdges.add(callEdge);
                            fullGraph.createCopiedEdge(callEdge);

                            final MethodGraph calledGraph = nodeToMethodGraphMap.get(callEdge.getEnd());
                            if (helperGraphs.add(calledGraph)) {
                                toCheckGraphs.add(calledGraph);
                            }
                        }

                    } else if (label instanceof MethodSkipEdge) {
                        final MethodSkipEdge mse = (MethodSkipEdge) label;
                        final Node returnNode = mse.getNode();
                        /*
                         * Sometimes, the corresponding return state was
                         * already deleted. Then, we don't need to check
                         *  this edge.
                         */
                        if (!oldToNewMap.containsKey(returnNode)) {
                            continue;
                        }
                        final Node endNode = edge.getEnd();
                        final Edge returnEdge = new Edge(returnNode, new MethodReturnEdge(), endNode);
                        fullGraph.createCopiedEdge(returnEdge);
                        incomingReturnEdges.add(returnEdge);
                    }
                }
            }
            problems.add(new JBCTerminationSCCProblem(sccSubGraph, fullGraph, sccGraphs, outgoingCallEdges,
                incomingReturnEdges, helperGraphs, sccAnnotations, null));
        }

        if (this.arguments.singleResultSystem) {
            final SCCAnnotations sccAnnotations = new SCCAnnotations(termGraph);

            for (final Class<? extends SCCAnalysis> analysis : this.sccAnalyses) {
                sccAnnotations.doAnalysis(analysis);
            }

            final JBCTerminationSCCProblem fullProblem =
                new JBCTerminationSCCProblem(termGraph, termGraph, new LinkedHashSet<>(
                    terminationGraph.getMethodGraphs()), Collections.<Edge>emptySet(), Collections.<Edge>emptySet(),
                    Collections.<MethodGraph>emptySet(), sccAnnotations,
                    terminationGraph.getStartGraph().getStartNode());

            return ResultFactory.proved(fullProblem, YNMImplication.SOUND, new TerminationGraphToSCCProof(1));
        }


        return ResultFactory.provedAnd(problems,
        //final Iterator<JBCTerminationSCCProblem> it = problems.iterator(); it.next(); it.next(); it.next();
        //final Iterator<JBCTerminationSCCProblem> it = problems.iterator(); it.next();
        //return ResultFactory.proved(it.next(),
            YNMImplication.SOUND,
            new TerminationGraphToSCCProof(problems.size()));
    }

    /**
     * A very fine proof.
     * @author Marc Brockschmidt
     */
    public class TerminationGraphToSCCProof extends DefaultProof {
        /** The index of this SCC. */
        private final int sccNumber;

        /**
         * @param sccN number of separate SCCs.
         */
        public TerminationGraphToSCCProof(final int sccN) {
            super();
            this.sccNumber = sccN;
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            if (this.sccNumber == 0) {
                return "Proven termination by absence of SCCs";
            } else {
                return "Splitted TerminationGraph to " + this.sccNumber + " SCCs" + ((this.sccNumber > 1) ? "s." : ".");
            }
        }
    }
}
