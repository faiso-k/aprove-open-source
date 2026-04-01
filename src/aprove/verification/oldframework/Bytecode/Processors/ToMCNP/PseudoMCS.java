package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * @author Matthias Hoelzel
 *
 */
public class PseudoMCS {
    public LinkedList<MCSNode> nodes;
    public LinkedList<Triple<MCSNode, ArrayList<AbstractConstraint> , MCSNode>> edges;

    /**
     * Constructor
     */
    public PseudoMCS() {
        this.nodes = new LinkedList<MCSNode>();
        this.edges = new LinkedList<Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode>>();
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder("PseudoMCS {\nNodes:\n");
        for (final MCSNode node : this.nodes) {
            result.append(node.toString());
            result.append('\n');
        }
        result.append("Edges:\n");
        for (final Triple<MCSNode, ArrayList<AbstractConstraint> , MCSNode> edge : this.edges) {
            result.append(edge.toString());
            result.append('\n');
        }
        result.append("}\n");
        return result.toString();
    }

    /**
     * Creates the dot string.
     * @return a string.
     */
    public String toDOT() {
        final StringBuilder result = new StringBuilder("digraph {\n");
        for (final MCSNode node : this.nodes) {
            result.append('\t');
            result.append(node.getDotRepresentation());
            result.append('\n');
        }
        for (final Triple<MCSNode, ArrayList<AbstractConstraint>, MCSNode> edge : this.edges) {
            final MCSNode left  = edge.getX();
            final List<AbstractConstraint> constraints = edge.getY();
            final MCSNode right = edge.getZ();

            result.append('\t');
            result.append(left.getDotName());
            result.append(" -> ");
            result.append(right.getDotName());
            result.append(" [label=\"");
            for (final AbstractConstraint c : constraints) {
                result.append(c.toString());
                result.append("\\n");
            }
            result.append("\"];\n");
        }
        result.append("};");
        return result.toString();
    }
}
