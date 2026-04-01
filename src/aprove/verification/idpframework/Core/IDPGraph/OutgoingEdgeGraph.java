package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class OutgoingEdgeGraph extends Graph<Set<IEdge>, IPosition> {

    private final Node<Set<IEdge>> root;

    public OutgoingEdgeGraph(final IDependencyGraph graph, final INode node) {
        this.root = new Node<Set<IEdge>>(new LinkedHashSet<IEdge>());
        this.addNode(this.root);

        final ImmutableMap<INode, ImmutableSet<IEdge>> successors = graph.getSuccessors(node);

        for (final ImmutableSet<IEdge> succEdges : successors.values()) {
            for (final IEdge succEdge : succEdges) {
                this.addEdge(succEdge);
            }
        }
    }

    private void addEdge(final IEdge edge) {
        Node<Set<IEdge>> parentNode = this.root;
        IPosition remainingPos = edge.fromPos;

        boolean foundNewParent;
        do {
            foundNewParent = false;

            for (final Edge<IPosition, Set<IEdge>> posEdge : this.getOutEdges(parentNode)) {
                if (posEdge.getObject().isPrefixOf(remainingPos)) {
                    parentNode = posEdge.getEndNode();
                    remainingPos = remainingPos.getShortestDifferentSufix(posEdge.getObject());
                    foundNewParent = true;
                    break;
                }
            }

        } while (foundNewParent && !remainingPos.isEmptyPosition());

        if (remainingPos.isEmptyPosition()) {
            parentNode.getObject().add(edge);
        } else {
            final Node<Set<IEdge>> newNode = new Node<Set<IEdge>>(new LinkedHashSet<IEdge>());
            newNode.getObject().add(edge);
            this.addEdge(parentNode, newNode, remainingPos);
        }

    }

    public Node<Set<IEdge>> getRoot() {
        return this.root;
    }

}
