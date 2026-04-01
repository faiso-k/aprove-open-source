package aprove.input.Programs.llvm.processors;

import aprove.Globals;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * 
 * This processor splits a given LLVMSEGraphProblem into several LLVMLassoProblems. 
 * A lasso is subgraph of the original graph which has a tail starting from the start node of the graph and a head which is a loop.
 * The parameter {@code loopfreeTails} (default: false) restricts the tails to not include other loops in its tail.
 * The loop free version is used for proving (non-)termination with T2, the loop included version is used for proving nontermination with LoAT.
 * 
 * @author Alex Hoppen, Jiong Fu, Constantin Mensendiek
 *
 */
public class LLVMSEGraphToLassoProcessor extends Processor.ProcessorSkeleton {

    /**
     * only include lassos with loop-free tails
     */
    private final boolean loopfreeTails;

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMSEGraphToLassoProcessor(LLVMSEGraphToLassoProcessor.Arguments arguments) {
        this.loopfreeTails = arguments.loopfreeTails;
    }

    public static class Arguments {

        /**
         * only include lassos with loop-free tails
         */
        public boolean loopfreeTails = true;

    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMSEGraphProblem);
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#process(aprove.prooftree.Obligations.BasicObligation, aprove.prooftree.Obligations.BasicObligationNode, aprove.strategies.Abortions.Abortion, aprove.strategies.ExecutableStrategies.RuntimeInformation)
     */
    @Override
    public Result process(
                          final BasicObligation obl,
                          final BasicObligationNode oblNode,
                          final Abortion aborter,
                          final RuntimeInformation rti) throws AbortionException {
        final LLVMSEGraph graph = ((LLVMSEGraphProblem) obl).getGraph();
        if (Globals.DEBUG_MARC) {
            graph.dumpGraph();
        }
        final List<LLVMSCCProblem> loopfreeProblems = new LinkedList<LLVMSCCProblem>();
        final List<LLVMSCCProblem> loopIncludedProblems = new LinkedList<LLVMSCCProblem>();
        final LinkedHashSet<Cycle<LLVMAbstractState>> sccs = graph.getSCCs();

        // iterate over all cycles
        for (final Cycle<LLVMAbstractState> s : sccs) {
            Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> entryEdges = s.getEntryEdges(graph);
            for (Edge<LLVMEdgeInformation, LLVMAbstractState> entryEdge : entryEdges) {
                aborter.checkAbortion();
                Set<List<Node<LLVMAbstractState>>> entryPaths = graph.getAllPaths(graph.getRoot(),
                                                                                  entryEdge.getEndNode());

                // iterate over all loop-free tails
                for (List<Node<LLVMAbstractState>> entryPathNodes : entryPaths) {

                    // add the lasso with the loop-free tail
                    List<Edge<LLVMEdgeInformation, LLVMAbstractState>> entryPath = getPathfromNodes(entryPathNodes,
                                                                                                    graph);
                    LLVMLassoProblem lassoProblem = new LLVMLassoProblem(graph.getSubGraph(s), entryPath, false);
                    lassoProblem.setParent(obl); // LLVM SCC problem is the parent of LLVM Lasso problem
                    loopfreeProblems.add(lassoProblem);

                    if (!this.loopfreeTails) {

                        List<Edge<LLVMEdgeInformation, LLVMAbstractState>> tailWithLoops =
                                                                                         addLoopsAlongTail(entryPathNodes,
                                                                                                           s,
                                                                                                           sccs,
                                                                                                           graph);

                        if (tailWithLoops.size() > entryPath.size()) {
                            lassoProblem = new LLVMLassoProblem(graph.getSubGraph(s), tailWithLoops, false);
                            lassoProblem.setParent(obl); // LLVM SCC problem is the parent of LLVM Lasso problem
                            loopIncludedProblems.add(lassoProblem);
                        }

                    }

                }
            }
        }

        if (this.loopfreeTails) {
            YNMImplication implication;
            boolean lassosIndependent = areLoopsIndependent(loopfreeProblems, graph);
            if (lassosIndependent) {
                implication = YNMImplication.EQUIVALENT;
            } else {
                // Transformation is no longer sound if the loops are not independent
                // since there may be a terminating run that is only possible by traversing
                // more than once and then continuing to another loop. This cannot be modelled
                // using lassos with loop-free finite tails
                implication = YNMImplication.COMPLETE;
            }
            return ResultFactory.provedAnd(loopfreeProblems,
                                           implication,
                                           new SymbolicExecutionGraphToLassoProof(loopfreeProblems.size(),
                                                                                  lassosIndependent));
        } else {

            final List<LLVMSCCProblem> problems = new LinkedList<LLVMSCCProblem>();
            problems.addAll(loopfreeProblems);
            problems.addAll(loopIncludedProblems);

            // should be <=>, but since ResultFactory does not work with MAYBE Result we need to take complete            
            //YNMImplication implication = YNMImplication.EQUIVALENT;
            YNMImplication implication = YNMImplication.COMPLETE;

            return ResultFactory.provedAnd(problems,
                                           implication,
                                           new SymbolicExecutionGraphToLassoProof(loopfreeProblems,
                                                                                  loopIncludedProblems));
        }

    }

    /**
     * gives a list of edges representing the tail with all loops that could be entered along the loop free path
     * 
     * @param <E> Edge type
     * @param <N> Node type
     * @param tailNodes the nodes of the loop free tail
     * @param lassoHead the head of the lasso which is a loop
     * @param sccs all loops to be considered to be added
     * @param graph the original graph
     * @return a new list of edges for the tail (potentially including loops)
     */
    public <E, N>
            List<Edge<E, N>>
            addLoopsAlongTail(List<Node<N>> tailNodes,
                              Cycle<N> lassoHead,
                              Set<Cycle<N>> sccs,
                              SimpleGraph<N, E> graph) {
        List<Edge<E, N>> tail = getPathfromNodes(tailNodes, graph);
        for (Cycle<N> ss : sccs) {
            if (ss != lassoHead) {
                for (Node<N> tailNode : tailNodes) {
                    if (ss.contains(tailNode)) {
                        tail.addAll(graph.getSubGraph(ss).getEdges());
                        //tail.addAll(getPathfromCycle(ss, tailNode, graph));
                        break;
                    }
                }
            }
        }
        return tail;
    }

    /**
     * gives the edges representing the loop. Note that the the first edge's start node and the last edge's end node are both the entry node.
     * 
     * @param <E> Edge type
     * @param <N> Node type
     * @param cycle a loop
     * @param entry the start node (needs to be element of the loop)
     * @param originalGraph the original graph
     * @return a list of edges representing the loop
     */
    public <E, N> List<Edge<E, N>> getPathfromCycle(Cycle<N> cycle, Node<N> entry, SimpleGraph<N, E> originalGraph) {
        List<Node<N>> temp = new LinkedList<>(cycle);
        List<Node<N>> list = new LinkedList<>();
        int start = temp.indexOf(entry);
        list.addAll(temp.subList(start, temp.size()));
        list.addAll(temp.subList(0, start + 1));
        return getPathfromNodes(list, originalGraph);
    }

    /**
     * gives a list of edges which connects two consecutive nodes of the given list. Only works if the edges exist in the original graph.
     * 
     * @param <E> Edge type
     * @param <N> Node type
     * @param nodes a list of nodes
     * @param originalGraph the original graph
     * @return a list of edges
     */
    public <E, N> List<Edge<E, N>> getPathfromNodes(List<Node<N>> nodes, SimpleGraph<N, E> originalGraph) {
        LinkedList<Edge<E, N>> path = new LinkedList<>();
        Node<N> previousNode = null;
        for (Node<N> node : nodes) {
            if (previousNode != null) {
                Edge<E, N> edge = originalGraph.getEdge(previousNode, node);
                path.add(edge);
            }
            previousNode = node;
        }
        return path;
    }

    /**
     * Checks if there is no path between the loops of any two problems
     * @param problems The problems for which to check whether they are independent
     * @param graph
     * @return <code>true</code> iff there is no path that connects the loops of any two problems
     */
    private boolean areLoopsIndependent(List<LLVMSCCProblem> problems, LLVMSEGraph graph) {
        for (LLVMSCCProblem problem1 : problems) {
            for (LLVMSCCProblem problem2 : problems) {
                if (problem1 == problem2) {
                    continue;
                }
                if (Globals.useAssertions) {
                    assert !problem1.getSCC().getNodes().isEmpty();
                    assert !problem2.getSCC().getNodes().isEmpty();
                }
                // Pick a node from each problem and check if there is a path
                // Picking an arbitrary node in the loop works, because the loop is a SCC
                Node<LLVMAbstractState> node1 = problem1.getSCC().getNodes().iterator().next();
                Node<LLVMAbstractState> node2 = problem2.getSCC().getNodes().iterator().next();
                if (graph.getPath(node1, node2) != null) {
                    return false;
                }
            }
        }
        return true;
    }

    public class SymbolicExecutionGraphToLassoProof extends DefaultProof {

        private String message;

        /**
         * @param numberOfLassos number of separate lassos
         * @param lassosIndependent Are all lassos independent of each other?
         */
        public SymbolicExecutionGraphToLassoProof(int numberOfLassos, boolean lassosIndependent) {
            super();
            this.message = "Converted SEGraph to " +
                           numberOfLassos
                           +
                           (lassosIndependent ? " independent" : " dependent")
                           +
                           " lasso"
                           +
                           ((numberOfLassos != 1) ? "s" : "")
                           +
                           ".";
        }

        public SymbolicExecutionGraphToLassoProof(List<LLVMSCCProblem> loopfreeProblems,
                                                  List<LLVMSCCProblem> loopIncludedProblems) {
            super();
            this.message = "Converted SEGraph to " +
                           loopfreeProblems.size()
                           +
                           " lassos with loop-free tails."
                           +
                           (loopIncludedProblems.isEmpty() ? ""
                                                           : "\nAdditionally, "
                                                             +
                                                             (loopIncludedProblems.size() == 1 ? "there is 1 lasso with loops in its tail."
                                                                                               : "there are "
                                                                                                 + loopIncludedProblems.size()
                                                                                                 + " lassos with loops in their tails."));
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return message;
        }

    }
}
