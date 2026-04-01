package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Collection of joins annotations in a given state.
 * @author Marc Brockschmidt
 */
public class JoiningStructures extends BinaryAnnotation implements Cloneable {
    /**
     * @param collection take all entries from this
     */
    private JoiningStructures(final Collection<TwoRefs> collection) {
        super(collection);
    }

    /**
     * Create an empty set of pairs of joining references.
     */
    public JoiningStructures() {
        this(Collections.<TwoRefs>emptySet());
    }

    /**
     * Returns a deep (!) copy of this {@link JoiningStructures} annotation
     * @return Deep copy of this object
     */
    @Override
    public JoiningStructures clone() {
        return new JoiningStructures(this.getCollection());
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    /**
     * Append a nice string representation to the string builder
     * @param sb a string builder
     */
    public void toString(final StringBuilder sb) {
        final SimpleGraph<AbstractVariableReference, Object> graph = super.getGraph();
        final Collection<Pair<Node<AbstractVariableReference>, Node<AbstractVariableReference>>> shown =
            new LinkedHashSet<>();
        final Collection<Collection<Node<AbstractVariableReference>>> cliques = graph.getCliques(3, true);
        if (cliques.size() > 0) {
            if (cliques.size() > 1) {
                sb.append("-><- Cliques:\n");
            } else {
                sb.append("-><- Clique: ");
            }
        }
        for (final Collection<Node<AbstractVariableReference>> clique : cliques) {
            for (final Pair<Node<AbstractVariableReference>, Node<AbstractVariableReference>> pair : Collection_Util
                .getPairs(clique))
            {
                shown.add(pair);
                shown.add(new Pair<>(pair.y, pair.x));
            }
            final Collection<AbstractVariableReference> refs = new LinkedHashSet<>();
            for (final Node<AbstractVariableReference> node : clique) {
                refs.add(node.getObject());
            }
            sb.append(refs);
            sb.append("\n");
        }

        // output the annotations which do not form a clique
        for (final Node<AbstractVariableReference> startNode : graph.getNodes()) {
            for (final Node<AbstractVariableReference> endNode : graph.getOut(startNode)) {
                if (!shown.add(new Pair<>(startNode, endNode))) {
                    continue;
                }
                sb.append(startNode.getObject());
                sb.append("->");
                sb.append("<-");
                sb.append(endNode.getObject());
                shown.add(new Pair<>(endNode, startNode));
                sb.append("\n");
            }
        }
    }

    /**
     * DO NOT MODIFY!
     * @return the all known joins annotations in this state
     */
    public Collection<TwoRefs> getJoinsAnnotations() {
        return super.getCollection();
    }

    /**
     * @param refA some reference
     * @param refB some other reference
     * @return true iff these two references are marked as possible joining
     */
    public boolean areJoining(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        return super.contains(refA, refB);
    }

    /**
     * Remove annotations that are useless.
     * @param state the state containing this object
     * @return true if something was removed
     */
    public boolean clean(final State state) {
        boolean annotationRemoved = false;

        final HeapAnnotations ha = state.getHeapAnnotations();

        final Iterator<TwoRefs> it = super.getCollection().iterator();
        while (it.hasNext()) {
            final TwoRefs twoRefs = it.next();
            final AbstractVariableReference refOne = twoRefs.getRefOne();
            final AbstractVariableReference refTwo = twoRefs.getRefTwo();

            // remove x -+><*- x for tree-shaped x
            if (refOne.equals(refTwo)) {
                if (!ha.isPossiblyNonTree(refOne)) {
                    it.remove();
                    annotationRemoved = true;
                    continue;
                }
            }

            // remove joins where both references are fully realized
            if (state.isFullyRealized(refOne) && state.isFullyRealized(refTwo)) {
                it.remove();
                annotationRemoved = true;
                continue;
            }
        }

        return annotationRemoved;
    }

    @Override
    protected String getAnnotationName() {
        return "maybe-join";
    }
}
