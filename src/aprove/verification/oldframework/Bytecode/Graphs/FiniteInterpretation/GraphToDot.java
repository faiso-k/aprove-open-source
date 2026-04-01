package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.io.IOException;
import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A simple helper class providing dot output for a method graph.
 * @author cotto
 */
public final class GraphToDot {
    /**
     * No. Just no.
     */
    private GraphToDot() {

    }

    /**
     * Append the format of the edge to the string builder
     * @param edge the first (and only?) edge
     * @param edgeInfos information on the edge(s)
     * @param sb a string builder
     * @throws IOException 
     */
    private static void addEdgeFormat(
            final Edge edge,
            final Collection<EdgeInformation> edgeInfos,
            final Appendable sb) throws IOException
    {
        final EdgeInformation edgeInfo = edge.getLabel();
        if (edgeInfo instanceof EvaluationEdge || edgeInfo instanceof CallAbstractEdge) {
            final String edgeColor = edgeInfo.getEdgeColor();
            sb.append(" [color=");
            sb.append(edgeColor);
            sb.append(", label=\"");
            for (final EdgeInformation ei : edgeInfos) {
                for (final VariableInformation i : ei) {
                    final String iString = i.toString();
                    if (iString.length() > 0) {
                        sb.append(iString).append("\\n");
                    }
                }
            }
            if (edgeInfo instanceof PredefinedMethodEdge) {
                sb.append(edgeInfo.toString()).append("\\n");
            }
            if (edge.getLabel() instanceof MethodStartEdge) {
                sb.append(edge.getLabel().toString());
            }
        } else if (edgeInfo instanceof RefinementOrSplitEdge) {
            sb.append(" [color="
                    + edgeInfo.getEdgeColor()
                    + ", label=\""
                    + ((RefinementOrSplitEdge) edgeInfo).getLabel());
            for (final EdgeInformation ei : edgeInfos) {
                for (final VariableInformation i : ei) {
                    final String iString = i.toString();
                    if (iString.length() > 0) {
                        sb.append(iString).append("\\n");
                    }
                }
            }
        } else if (edgeInfo instanceof InstanceEdge) {
            final String label = edgeInfo.toString();
            sb.append(" [color=" + edgeInfo.getEdgeColor() + ", label=\"" + label);
        } else if (edgeInfo instanceof DebugEdge) {
            sb.append(" [color=" + edgeInfo.getEdgeColor() + ", label=\"" + edgeInfo.toString());
        } else {
            sb.append(" [color=" + edgeInfo.getEdgeColor() + ", label=\"");
        }
        sb.append("\"];\n");
    }

    /**
     * @return the node at the (shown) end of the given edge, which may skip
     * some evaluation edges if the corresponding option is set. Furthermore,
     * the labels on the edge(s) are returned.
     * @param edge the edge starting in the start node
     * @param nodes the relevant nodes
     */
    private static Pair<Node, Collection<EdgeInformation>> findEndNode(final Edge edge, final Collection<Node> nodes) {
        final EdgeInformation edgeInfo = edge.getLabel();
        final Collection<EdgeInformation> edgeInfos = new LinkedHashSet<>();
        edgeInfos.add(edge.getLabel());

        Node childNode = edge.getEnd();

        if (JBCOptions.MERGE_METHODSKIPS && edgeInfo instanceof MethodSkipEdge) {
            OUTER: while (!nodes.contains(childNode)) {
                for (final Edge out : childNode.getOutEdges()) {
                    if (out.getLabel() instanceof InstanceEdge) {
                        childNode = out.getEnd();
                        edgeInfos.add(out.getLabel());
                        continue OUTER;
                    }
                    return new Pair<>(null, null);
                }
                return new Pair<>(null, null);
            }
        } else if (JBCOptions.MERGE_EVALS && edgeInfo instanceof EvaluationEdge) {
            OUTER: while (!nodes.contains(childNode)) {
                for (final Edge out : childNode.getOutEdges()) {
                    if (out.getLabel() instanceof EvaluationEdge) {
                        childNode = out.getEnd();
                        edgeInfos.add(out.getLabel());
                        continue OUTER;
                    }
                    return new Pair<>(null, null);
                }
                return new Pair<>(null, null);
            }
        }

        return new Pair<Node, Collection<EdgeInformation>>(childNode, edgeInfos);
    }

    private static boolean printEdge(
            final Edge edge,
            final boolean isHiddenedge,
            final Set<Node> nodes,
            final Appendable sb) throws IOException
    {
        // Now generate edges, format:
        // FATHER -> CHILD [INFORMATION];
        final Node currentNode = edge.getStart();
        if (!nodes.contains(currentNode)) {
            return false;
        }

        // for method skip edges and MERGE_EVALS we must skip some edges
        final Pair<Node, Collection<EdgeInformation>> pair = GraphToDot.findEndNode(edge, nodes);
        final Node endNode = pair.x;
        final Collection<EdgeInformation> edgeInfos = pair.y;

        if (!nodes.contains(endNode)) {
            return false;
        }

        sb.append(Integer.toString(currentNode.getNodeNumber()));
        sb.append(" -> ");
        sb.append(Integer.toString(endNode.getNodeNumber()));
        GraphToDot.addEdgeFormat(edge, edgeInfos, sb);
        return true;
    }

    private static boolean printNode(
            final Node currentNode,
            final boolean isHiddenNode,
            final Appendable sb,
            final AdditionalNodeInfoProvider nodeInfoProvider) throws IOException
    {

        if (JBCOptions.HIDE_EXCEPTION_STATES) {
            State currentState = currentNode.getState();
            if (currentState.getCallStack().getStackFrameList().stream().anyMatch(x -> x.hasException())) {
                return false;
            } else if (currentState.getCallStack().isEmpty()) {
                boolean skip = true;
                for (Edge e : currentNode.getInEdges()) {
                    State startState = e.getStart().getState();
                    skip &= startState.getCallStack().getStackFrameList().stream().anyMatch(x -> x.hasException());
                }
                if (skip) {
                    return false;
                }
            }
        }
        boolean show = !JBCOptions.MERGE_EVALS;
        final StringBuilder nodeString = new StringBuilder();
        nodeString.append(currentNode.getNodeNumber() + " [");
        String format = "";
        String nodeLabel = "";
        boolean noIncomingEdge = true;
        boolean isMethodSkip = false;
        Set <Edge> inEdges = isHiddenNode ? currentNode.getHiddenInEdges() : currentNode.getInEdges();
        for (final Edge e : inEdges) {
            noIncomingEdge = false;
            final EdgeInformation edge = e.getLabel();
            if (!(edge instanceof EvaluationEdge)) {
                if (edge instanceof MethodSkipEdge) {
                    final MethodSkipEdge mse = (MethodSkipEdge) edge;
                    if (mse.getNode() == null) {
                        nodeLabel = nodeLabel + "return from deleted node\\n";
                    } else {
                        nodeLabel = nodeLabel + "return from node " + mse.getNode().getNodeNumber() + "\n";
                    }
                    show = true;
                    if (JBCOptions.MERGE_METHODSKIPS) {
                        isMethodSkip = true;
                        show = false;
                    }
                } else {
                    show = true;
                }
            }
            if (isHiddenNode) {
                format = format + ", color=" + JBCOptions.COLOR_DELETED;
                format = format + ", style=diagonals";
            } else {
                format = ", " + edge.getNodeFormat();
            }
        }

        if (nodeInfoProvider != null) {
            final String color = nodeInfoProvider.getColor(currentNode);
            if (color != null) {
                format = ", color = \"" + color + "\", style = filled";
            }
        }

        nodeLabel += currentNode.getNodeNumber() + ": " + currentNode.getState().toString();
        nodeLabel = nodeLabel.replace("\n", "\\n").replace("\"", "\\\"").replace("\\{", "\\\\{");

        String prepend;
        String append;
        if (nodeInfoProvider != null) {
            prepend = nodeInfoProvider.getPrependString(currentNode);
            append = nodeInfoProvider.getAppendString(currentNode);
        } else {
            append = "";
            prepend = "";
        }

        nodeString.append("label=\"" + prepend + nodeLabel + append + "\"");
        nodeString.append(format);
        nodeString.append("];\n");

        /*
         * If evaluation edges are skipped, we need to find out when to stop
         * skipping (i.e., when to display the node). Furthermore, we only
         * show results of a method skip if there is no outgoing instance
         * edge.
         */
        if (show || noIncomingEdge || currentNode.getOutEdges().isEmpty()) {
            show = true;
        } else {
            for (final Edge e : currentNode.getOutEdges()) {
                if (isMethodSkip) {
                    if (!(e.getLabel() instanceof InstanceEdge)) {
                        show = true;
                        break;
                    }
                } else if (!(e.getLabel() instanceof EvaluationEdge)) {
                    show = true;
                    break;
                }
            }
        }
        if (show) {
            sb.append(nodeString.toString());
        }
        return show;
    }

    /**
     * Append the dot output for the method graph to the string builder
     * @param graph the method graph
     * @param sb the string builder
     * @param nodeInfoProvider if non-null, gives text to prepend, text to append and a color for each node
     * @throws IOException 
     */
    public static void toDot(
            final JBCGraph graph,
            final Appendable sb,
            final AdditionalNodeInfoProvider nodeInfoProvider) throws IOException
    {
        // find the nodes we want to show and append the dot definitions
        final Set<Node> nodes = new LinkedHashSet<>();
        for (final Node currentNode : graph.getNodes()) {
            if (printNode(currentNode, false, sb, nodeInfoProvider)) {
                nodes.add(currentNode);
            }
        }
        if (JBCOptions.SHOW_HIDDEN && graph instanceof MethodGraph) {
            for (final Node currentNode : ((MethodGraph) graph).getHiddenNodes()) {
                if (printNode(currentNode, true, sb, nodeInfoProvider)) {
                    nodes.add(currentNode);
                }
            }
        }

        for (final Edge edge : graph.getEdges()) {
            printEdge(edge, false, nodes, sb);
        }
        if (JBCOptions.SHOW_HIDDEN && graph instanceof MethodGraph) {
            for (final Edge edge : ((MethodGraph) graph).getHiddenEdges()) {
                printEdge(edge, true, nodes, sb);
            }
        }
    }
}
