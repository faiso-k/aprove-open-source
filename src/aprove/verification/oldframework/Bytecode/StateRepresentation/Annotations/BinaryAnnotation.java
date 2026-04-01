package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;
import java.util.stream.Collectors;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Implementations are annotations dealing with two references, e.g. "x joins y" or "x =?= y".
 * @author cotto
 */
public abstract class BinaryAnnotation {
    /**
     * A collection of two references x, y.
     */
    private final Collection<TwoRefs> coll;

    /**
     * @param refs pairs of references
     */
    public BinaryAnnotation(final Collection<TwoRefs> refs) {
        this.coll = new LinkedHashSet<>(refs);
    }

    /**
     * Note a REL b
     * @param varRefA Guess from the description.
     * @param varRefB Guess from the description.
     * @return true iff this was a new annotation
     */
    public boolean add(final AbstractVariableReference varRefA, final AbstractVariableReference varRefB) {
        if (varRefA == null || varRefB == null) {
            return false;
        }
        if (varRefA.isNULLRef() || varRefB.isNULLRef()) {
            return false;
        }

        return this.coll.add(new TwoRefs(varRefA, varRefB));
    }

    /**
     * Removes all stored information.
     */
    public void clear() {
        this.coll.clear();
    }

    /**
     * @param refA a reference
     * @param refB another reference
     * @return true iff this contains refA REL refB
     */
    public boolean contains(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        if (refA == null || refB == null) {
            return false;
        }
        return this.coll.contains(new TwoRefs(refA, refB));
    }

    /**
     * @return the internal data structure, DO NOT MODIFY
     */
    public Collection<TwoRefs> getCollection() {
        return this.coll;
    }

    /**
     * @return a graph representation of the stored relations
     */
    SimpleGraph<AbstractVariableReference, Object> getGraph() {
        // for each set of connecting fields build a graph to find cliques
        final Object dummy = new Object();
        final Map<AbstractVariableReference, Node<AbstractVariableReference>> nodeMap = new TreeMap<>();
        final SimpleGraph<AbstractVariableReference, Object> graph = new SimpleGraph<>();
        for (final TwoRefs twoRefs : this.getCollection()) {
            final AbstractVariableReference key = twoRefs.getRefOne();
            Node<AbstractVariableReference> start = nodeMap.get(key);
            if (start == null) {
                start = new Node<>(key);
                nodeMap.put(key, start);
            }
            final AbstractVariableReference value = twoRefs.getRefTwo();
            Node<AbstractVariableReference> end = nodeMap.get(value);
            if (end == null) {
                end = new Node<>(value);
                nodeMap.put(value, end);
            }
            graph.addEdge(start, end, dummy);
            graph.addEdge(end, start, dummy);
        }

        return graph;
    }

    /**
     * @return a collection containing all references
     */
    public Collection<AbstractVariableReference> getReferences() {
        final Collection<AbstractVariableReference> res = new LinkedHashSet<>();
        for (final TwoRefs twoRefs : this.coll) {
            res.add(twoRefs.getRefOne());
            res.add(twoRefs.getRefTwo());
        }
        return res;
    }

    /**
     * @param varRef an {@link AbstractVariableReference} for which we return all references a with varRef REL a
     * @return Set of all such references a.
     */
    public Collection<AbstractVariableReference> getReferencesWithPartner(final AbstractVariableReference varRef) {
        final Collection<AbstractVariableReference> res = new LinkedHashSet<>();
        for (final TwoRefs twoRefs : this.coll) {
            if (twoRefs.forRef(varRef)) {
                res.add(twoRefs.getOther(varRef));
            }
        }
        return res;
    }

    /**
     * Remove everything we know about an {@link AbstractVariableReference}.
     * @param ref the {@link AbstractVariableReference} to remove.
     */
    public void remove(final AbstractVariableReference ref) {
        final Iterator<TwoRefs> it = this.coll.iterator();
        while (it.hasNext()) {
            final TwoRefs twoRefs = it.next();
            if (twoRefs.forRef(ref)) {
                it.remove();
            }
        }
    }

    /**
     * Remove refA REL refB
     * @param refA some reference
     * @param refB some reference
     * @return true iff removed
     */
    public boolean remove(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        if (refA == null || refB == null) {
            return false;
        }
        return this.coll.remove(new TwoRefs(refA, refB));
    }

    /**
     * Replace all information about a certain {@link AbstractVariableReference} with information about another
     * {@link AbstractVariableReference}.
     * @param toReplace the {@link AbstractVariableReference} to replace.
     * @param replacement the {@link AbstractVariableReference} to replace it with.
     */
    public void replace(final AbstractVariableReference toReplace, final AbstractVariableReference replacement) {
        if (replacement.isNULLRef()) {
            this.remove(toReplace);
            return;
        }

        final Collection<AbstractVariableReference> forToReplace = new LinkedHashSet<>();

        final Iterator<TwoRefs> it = this.coll.iterator();
        while (it.hasNext()) {
            final TwoRefs twoRefs = it.next();
            if (twoRefs.forRef(toReplace)) {
                it.remove();
                forToReplace.add(twoRefs.getOther(toReplace));
            }
        }

        if (forToReplace.isEmpty()) {
            return;
        }
        for (final AbstractVariableReference other : forToReplace) {
            if (other.equals(toReplace)) {
                this.add(replacement, replacement);
            } else {
                this.add(replacement, other);
            }
        }
    }

    public Collection<String> toSExpStrings() {
        final List<String> res = new LinkedList<>();
        String thisAnnotationName = this.getAnnotationName();
        for (TwoRefs tR : this.coll) {
            res.add("(" + thisAnnotationName + " " + tR.getRefOne().toString() + " " + tR.getRefTwo().toString() + ")");
        }
        return res;
    }

    /**
     * @param refA some reference
     * @param refB some other reference
     * @return true iff there is a node c which is reachable from refA and refB
     */
    public boolean hasCommonSuccessor(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        SimpleGraph<AbstractVariableReference, Object> graph = getGraph();
        Set<Node<AbstractVariableReference>> nodesA = graph.getNodes().stream().filter(x -> x.getObject() == refA).collect(
                Collectors.toSet());
        Set<Node<AbstractVariableReference>> nodesB = graph.getNodes().stream().filter(x -> x.getObject() == refB).collect(Collectors.toSet());
        if (nodesA.isEmpty() || nodesB.isEmpty()) {
            return false;
        }
        if (nodesA.size() > 1 || nodesB.size() > 1) {
            throw new IllegalStateException();
        }
        Set<Node<AbstractVariableReference>> reachableA = graph.determineReachableNodes(nodesA);
        Set<Node<AbstractVariableReference>> reachableB = graph.determineReachableNodes(nodesB);
        reachableA.retainAll(reachableB);
        return reachableA.size() > 0;
    }

    protected abstract String getAnnotationName();
}
