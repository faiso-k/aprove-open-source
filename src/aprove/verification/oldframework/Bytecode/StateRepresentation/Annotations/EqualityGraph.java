package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This graph is used to represent which references may be equal. The underlying graph is undirected, so we add edges in
 * both directions.
 * @author cotto
 */
public class EqualityGraph extends BinaryAnnotation implements Cloneable {
    /**
     * @param collection take all entries from this
     */
    private EqualityGraph(final Collection<TwoRefs> collection) {
        super(collection);
    }

    /**
     * Create an empty set of pairs of possibly equal references.
     */
    public EqualityGraph() {
        this(Collections.<TwoRefs>emptySet());
    }

    /**
     * @return a clone of this graph
     */
    @Override
    public EqualityGraph clone() {
        return new EqualityGraph(this.getCollection());
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
        final Collection<Set<AbstractVariableReference>> inClique = new LinkedHashSet<>();
        final Collection<Collection<Node<AbstractVariableReference>>> cliques = graph.getCliques(3, true);

        if (cliques.size() > 0) {
            if (cliques.size() < 2) {
                sb.append("=?= Clique: ");
            } else {
                sb.append("=?= Cliques:\n");
            }
        }
        for (final Collection<Node<AbstractVariableReference>> clique : cliques) {
            final Collection<AbstractVariableReference> refs = new LinkedHashSet<>();
            for (final Node<AbstractVariableReference> node : clique) {
                refs.add(node.getObject());
            }
            sb.append(refs);
            sb.append("\n");
            for (final Pair<Node<AbstractVariableReference>, Node<AbstractVariableReference>> pair : Collection_Util
                .getPairs(clique))
            {
                final Set<AbstractVariableReference> coll = new LinkedHashSet<>(2);
                coll.add(pair.x.getObject());
                coll.add(pair.y.getObject());
                inClique.add(coll);
            }
        }
        for (final Node<AbstractVariableReference> node : graph.getNodes()) {
            final Iterator<Node<AbstractVariableReference>> it = graph.getOut(node).iterator();
            final Collection<AbstractVariableReference> eqPartners = new TreeSet<>();

            while (it.hasNext()) {
                final Node<AbstractVariableReference> outNode = it.next();
                final Set<AbstractVariableReference> coll = new LinkedHashSet<>(2);
                coll.add(node.getObject());
                coll.add(outNode.getObject());
                if (inClique.contains(coll)) {
                    continue;
                }
                //As we have two edges to emulate an undirected graph, we use the node number
                //to select only one of these edges to display
                if (outNode.getNodeNumber() > node.getNodeNumber()) {
                    eqPartners.add(outNode.getObject());
                }
            }

            if (!eqPartners.isEmpty()) {
                final Iterator<AbstractVariableReference> partnerIt = eqPartners.iterator();
                sb.append(node.getObject()).append(" =?= ");
                while (partnerIt.hasNext()) {
                    sb.append(partnerIt.next());
                    if (partnerIt.hasNext()) {
                        sb.append(", ");
                    }
                }
                sb.append("\n");
            }
        }
    }

    /**
     * Replace oldRef by newRef
     * @param oldRef a reference
     * @param newRef another reference
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        super.replace(oldRef, newRef);

        // Ensure that no loop from newRef to newRef exists
        this.remove(newRef, newRef);
    }

    /**
     * Add an edge to the graph of possible equalities.
     * @param state state which is used for several sanity checks (to avoid equality annotations for references for
     * which conflicting information is known)
     * @param refOne a reference
     * @param refTwo another reference
     * @return true iff the edge did not exist before
     */
    public boolean addPossibleEquality(
        final State state,
        final AbstractVariableReference refOne,
        final AbstractVariableReference refTwo)
    {

        if (EqualityGraph.equalityUnneeded(refOne, refTwo, state)) {
            return false;
        }

        final boolean added = this.add(refOne, refTwo);
        return added;
    }

    /**
     * @return true only if it does not make sense to add refOne =?= refTwo, e.g. because one of them is the null
     * pointer.
     */
    private static boolean equalityUnneeded(
        final AbstractVariableReference refOne,
        final AbstractVariableReference refTwo,
        final State state)
    {
        if (refOne.equals(refTwo)) {
            return true;
        }
        if (refOne.isNULLRef() || refTwo.isNULLRef()) {
            return true;
        }
        final AbstractVariable varOne = state.getAbstractVariable(refOne);
        if (varOne != null) {
            if (varOne instanceof AbstractNumber) {
                return true;
            }
            if (varOne.isNULL()) {
                return true;
            }
        }
        final AbstractVariable varTwo = state.getAbstractVariable(refTwo);
        if (varTwo != null) {
            if (varTwo instanceof AbstractNumber) {
                return true;
            }
            if (varTwo.isNULL()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Add an edge connecting the two given references
     * @param refOne a reference
     * @param refTwo another reference
     * @return true iff this edge did not exist before
     */
    @Override
    public boolean add(final AbstractVariableReference refOne, final AbstractVariableReference refTwo) {
        if (refOne.equals(refTwo)) {
            return false;
        }
        return super.add(refOne, refTwo);
    }

    /**
     * @param refA some reference
     * @param refB another reference
     * @return true iff there is a direct, not transitive, possible equality is noted for refA and refB.
     */
    public boolean areMarkedAsPossiblyEqual(final AbstractVariableReference refA, final AbstractVariableReference refB)
    {
        return super.contains(refA, refB);
    }

    /**
     * Removes all noted equalities for which other information indicates that they are not possible (incompatible
     * types, ...).
     * @param state the state in which information about the containend elements is stored.
     * @return true if any annotation was removed (e.g. because we inferred it is not possible).
     */
    public boolean clean(final State state) {

        final LinkedList<Pair<AbstractVariableReference, AbstractVariableReference>> toRemove = new LinkedList<>();

        for (final TwoRefs twoRefs : super.getCollection()) {
            final AbstractVariableReference lhs = twoRefs.getRefOne();
            final AbstractVariableReference rhs = twoRefs.getRefTwo();

            // remove x =?= y if the types are not compatible
            final AbstractType lhsInstanceType = state.getAbstractType(lhs);
            final AbstractType rhsInstanceType = state.getAbstractType(rhs);
            if (lhsInstanceType == null || rhsInstanceType == null || lhs.isNULLRef() || rhs.isNULLRef()) {
                toRemove.add(new Pair<>(lhs, rhs));
            } else {
                if (!state.getCallStack().isEmpty()) {
                    final ClassPath cPath = state.getClassPath();

                    /*
                     * We want to check if all objects that are marked as possibly equal actually have abstract types
                     * with a non-empty intersection (e.g. both can have the same type). As the abstract type is already
                     * a safe approximation of a certain property of our reference types, we can infer inequality if the
                     * known information is conflicting.
                     */
                    if (!lhsInstanceType.hasIntersectionWith(rhsInstanceType, cPath, state.getJBCOptions())) {
                        toRemove.add(new Pair<>(lhs, rhs));
                    }
                }
            }
        }

        for (final Pair<AbstractVariableReference, AbstractVariableReference> removeMe : toRemove) {
            this.remove(removeMe.x, removeMe.y);
        }
        return !toRemove.isEmpty();
    }

    /**
     * @param ref a reference
     * @return all references x with ref =?= x
     */
    public Collection<AbstractVariableReference> getPartners(final AbstractVariableReference ref) {
        return super.getReferencesWithPartner(ref);
    }

    @Override
    protected String getAnnotationName() {
        return "maybe-equal";
    }
}
