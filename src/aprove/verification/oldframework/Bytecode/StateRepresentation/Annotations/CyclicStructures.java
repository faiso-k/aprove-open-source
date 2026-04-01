package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Collection of cyclic annotations in a given state.
 *
 * @author Marc Brockschmidt
 */
public class CyclicStructures implements Cloneable {
    /**
     * The actual references for which we know or suspect that they are cyclic.
     */
    private LinkedHashMap<AbstractVariableReference, CyclicAnnotation> cyclicRefs;

    /**
     * Create a new instance of this annotation-holding class.
     */
    public CyclicStructures() {
        this.cyclicRefs = new LinkedHashMap<>();
    }

    /**
     * Returns a deep (!) copy of this {@link CyclicStructures} annotation
     * @return Deep copy of this object
     */
    @Override
    public CyclicStructures clone() {
        CyclicStructures clone = null;

        try {
            clone = (CyclicStructures) super.clone();
        } catch (final CloneNotSupportedException e) {
            assert (false) : "java.lang.Object doesn't support cloning anymore";
        }

        clone.cyclicRefs = new LinkedHashMap<>();
        for (final Map.Entry<AbstractVariableReference, CyclicAnnotation> e : this.cyclicRefs.entrySet()) {
            clone.cyclicRefs.put(e.getKey(), e.getValue());
        }

        return clone;
    }

    /**
     * Remove everything we know about an {@link AbstractVariableReference}.
     * @param id the {@link AbstractVariableReference} to remove.
     * @return true iff the entry existed before removal
     */
    public boolean remove(final AbstractVariableReference id) {
        return this.cyclicRefs.remove(id) != null;
    }

    /**
     * Replace all information about a certain {@link AbstractVariableReference}
     * with information about another {@link AbstractVariableReference}.
     * @param toReplace the {@link AbstractVariableReference} to replace.
     * @param replacement the {@link AbstractVariableReference} to replace it
     *  with.
     */
    public void replace(final AbstractVariableReference toReplace, final AbstractVariableReference replacement) {
        if (this.cyclicRefs.containsKey(toReplace)) {
            //Don't add NULL@:
            if (!replacement.isNULLRef()) {
                this.cyclicRefs.put(replacement, new CyclicAnnotation(replacement, this.cyclicRefs
                    .get(toReplace)
                    .getNeededEdges()));
            }
            this.cyclicRefs.remove(toReplace);
        }
    }

    /**
     * <b>DO NOT USE DIRECTLY! Call State.setPossiblyCyclic() instead.</b><br>
     * Note a@.
     * @param ref Guess from the description.
     * @param neededE heap edges that must exist on any cycle involving ref.
     * @return true iff this was a new cyclic annotation (also true if the set
     * of needed edges got smaller)
     */
    public boolean add(final AbstractVariableReference ref, final Collection<HeapEdge> neededE) {
        assert (!neededE.contains(UnknownArrayMemberEdge.INSTANCE));
        final Set<HeapEdge> newNeededE = new LinkedHashSet<>();

        /*
         * Check if already have information about ref. If yes, we need to
         * construct the intersection of the two "must-have" field sets:
         */
        if (this.cyclicRefs.containsKey(ref)) {
            final ImmutableSet<HeapEdge> oldNeededE = this.cyclicRefs.get(ref).getNeededEdges();
            newNeededE.addAll(oldNeededE);
            newNeededE.retainAll(neededE);
            this.cyclicRefs.put(ref, new CyclicAnnotation(ref, newNeededE));
            return !newNeededE.equals(oldNeededE);
        }
        newNeededE.addAll(neededE);
        this.cyclicRefs.put(ref, new CyclicAnnotation(ref, newNeededE));
        return true;
    }

    /**
     * For a variable reference a, get all heap edges needed on a cycle involving
     * a.
     * @param varRef an {@link AbstractVariableReference} for which we look for
     *  needed edges.
     * @return Set of edges that need to exist on any cycle involving ref. May
     *  be empty.
     */
    public ImmutableSet<HeapEdge> getNeededEdgesOf(final AbstractVariableReference varRef) {
        return this.cyclicRefs.get(varRef).getNeededEdges();
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb, true);
        return sb.toString();
    }

    /**
     * Append a nice string representation to the string builder
     * @param sb a string builder
     * @param includeEmptyFieldSet if false, the entries @[] will not be shown
     */
    public void toString(final StringBuilder sb, final boolean includeEmptyFieldSet) {
        final CollectionMap<ImmutableSet<HeapEdge>, CyclicAnnotation> edges = new CollectionMap<>();
        for (final CyclicAnnotation t : this.cyclicRefs.values()) {
            if (includeEmptyFieldSet || !t.getNeededEdges().isEmpty()) {
                edges.add(t.getNeededEdges(), t);
            }
        }
        for (final Entry<ImmutableSet<HeapEdge>, Collection<CyclicAnnotation>> x : edges.entrySet()) {
            final Collection<CyclicAnnotation> annotations = x.getValue();
            if (annotations.size() > 1) {
                sb.append("@");
                sb.append(x.getKey());
                sb.append(": ");
                final Iterator<CyclicAnnotation> it = annotations.iterator();
                while (it.hasNext()) {
                    final CyclicAnnotation c = it.next();
                    sb.append(c.ref);
                    if (it.hasNext()) {
                        sb.append(", ");
                    }
                }
                sb.append("\n");
            } else {
                for (final CyclicAnnotation t : annotations) {
                    t.toString(sb);
                    sb.append("\n");
                }
            }
        }
    }

    /**
     * @param ref some reference
     * @return true iff this reference is marked as possibly cyclic
     */
    public boolean isCyclic(final AbstractVariableReference ref) {
        return this.cyclicRefs.containsKey(ref);
    }

    /**
     * @return set of all references for which we have a cyclic annotation. Do
     *  not modify!
     */
    public Set<AbstractVariableReference> getCyclicRefs() {
        return this.cyclicRefs.keySet();
    }

    /**
     * Removes all stored information.
     */
    public void clear() {
        this.cyclicRefs.clear();
    }

    public Collection<String> toSExpStrings() {
        final List<String> res = new LinkedList<>();
        for (Entry<AbstractVariableReference, CyclicAnnotation> e : this.cyclicRefs.entrySet()) {
            final AbstractVariableReference ref = e.getKey();
            final CyclicAnnotation cA = e.getValue();
            final StringBuilder s = new StringBuilder();
            s.append("(maybe-cyclic ");
            s.append(ref.toString());
            s.append(" (");
            boolean firstField = true;
            for (HeapEdge f : cA.getNeededEdges()) {
                if (firstField) {
                    firstField = false;
                } else {
                    s.append(" ");
                }
                s.append(f.getIdentifier().toString());
            }
            s.append("))");
            res.add(s.toString());
        }
        return res;
    }
}
