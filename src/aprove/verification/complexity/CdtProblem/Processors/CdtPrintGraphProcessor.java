package aprove.verification.complexity.CdtProblem.Processors;

import java.io.*;
import java.util.*;

import aprove.logging.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.Graph.*;

/* Just for debug - prints the dot output of the graph */
public class CdtPrintGraphProcessor extends CdtProblemProcessor {

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter) {
        CdtPrintGraphProcessor.outputGraphs(cdtProblem);
        return ResultFactory.unsuccessful();
    }

    public static void outputGraphs(CdtProblem cdtProblem) {
        PrintStream st = AproveOutput.openPrintStream("graph-" + cdtProblem.getId());
        st.print(cdtProblem.toDOT());
        st.close();
        st = AproveOutput.openPrintStream("sccGraph-" + cdtProblem.getId());
        st.print(CdtPrintGraphProcessor.getSccGraph(cdtProblem.getGraph().getCopyOfGraph()).toDOT());
        st.close();
    }

    /**
     * Creates a graph were each node is a SCC in the original graph.
     * Two nodes are connected iff the SCCs are connected.
     *
     * Each node is labeled with the size of the SCC
     */
    private static <N,E> Graph<Integer,Void> getSccGraph(Graph<N,E> graph) {
        LinkedHashSet<Cycle<N>> mathSccs = graph.getSCCs(false);

        Set<Node<Integer>> newNodes = new LinkedHashSet<Node<Integer>>();
        Map<Node<N>, Node<Integer>> sccNode2newNode =
            new LinkedHashMap<Node<N>, Node<Integer>>();
        for (Cycle<N> scc : mathSccs) {
            Node<Integer> newNode = new Node<Integer>(scc.size());
            newNodes.add(newNode);
            for (Node<N> n : scc) {
                sccNode2newNode.put(n, newNode);
            }
        }

        Graph<Integer, Void> newGraph =
            new Graph<Integer, Void>(newNodes);

        for (Cycle<N> scc : mathSccs) {
            Node<Integer> newNode = sccNode2newNode.get(scc.iterator().next());
            Set<Node<N>> outNodes = new LinkedHashSet<Node<N>>();
            for (Node<N> n : scc) {
                outNodes.addAll(graph.getOut(n));
            }
            for (Node<N> n : outNodes) {
                newGraph.addEdge(newNode, sccNode2newNode.get(n));
            }
        }

        return newGraph;
    }
}
