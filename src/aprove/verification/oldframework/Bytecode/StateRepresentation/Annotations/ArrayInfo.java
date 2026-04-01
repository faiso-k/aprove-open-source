package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * We sometimes know that an abstract array a has content o at index i (a[i] = o).
 */
public class ArrayInfo implements Cloneable {
    /**
     * The actual data (array -> index -> content).
     */
    private final Map<AbstractVariableReference, Map<AbstractVariableReference, AbstractVariableReference>> map =
        new LinkedHashMap<>();

    /**
     * Remember that array[index] = content holds
     * @param arrayRef the array
     * @param indexRef the index
     * @param contentRef the content
     */
    public void add(final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef,
        final AbstractVariableReference contentRef) {
        assert (indexRef.pointsToInteger());
        assert (arrayRef.pointsToReferenceType() && !arrayRef.isNULLRef());

        Map<AbstractVariableReference, AbstractVariableReference> innerMap = this.map.get(arrayRef);
        if (innerMap == null) {
            innerMap = new LinkedHashMap<>();
            this.map.put(arrayRef, innerMap);
        }
        innerMap.put(indexRef, contentRef);
    }

    /**
     * Add the information for ref which is stored in the source object.
     * @param source some array information from which we copy
     * @param arrayRef the array reference for which we copy the information
     */
    public void addAllDataFrom(final ArrayInfo source, final AbstractVariableReference arrayRef) {
        final Map<AbstractVariableReference, AbstractVariableReference> innerMap = source.map.get(arrayRef);
        if (innerMap != null) {
            for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entry : innerMap.entrySet()) {
                this.add(arrayRef, entry.getKey(), entry.getValue());
            }
        }
    }

    /**
     * Remove annotations that are useless.
     * @param refsToRemove the references that are removed from the state
     * @param state the state for which this information is used (may be null)
     * @return true if something was removed
     */
    public boolean clean(final Collection<AbstractVariableReference> refsToRemove, final State state) {
        boolean changed = false;
        for (final AbstractVariableReference ref : refsToRemove) {
            changed |= this.map.remove(ref) != null;
        }

        final Collection<AbstractVariableReference> removeOuter = new LinkedHashSet<>();
        if (state != null) {
            for (final AbstractVariableReference arrayRef : this.map.keySet()) {
                final AbstractVariable var = state.getAbstractVariable(arrayRef);
                if (var instanceof ConcreteArray) {
                    removeOuter.add(arrayRef);
                }
            }
            for (final AbstractVariableReference ref : removeOuter) {
                changed = true;
                this.map.remove(ref);
            }

            removeOuter.clear();
        }

        for (final Map.Entry<AbstractVariableReference, Map<AbstractVariableReference, AbstractVariableReference>> entry : this.map.entrySet()) {
            final Map<AbstractVariableReference, AbstractVariableReference> innerMap = entry.getValue();
            for (final AbstractVariableReference ref : refsToRemove) {
                changed |= innerMap.remove(ref) != null;
            }
            final Collection<AbstractVariableReference> removeInner = new LinkedHashSet<>();
            for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> innerEntry : innerMap.entrySet()) {
                if (refsToRemove.contains(innerEntry.getValue())) {
                    removeInner.add(innerEntry.getKey());
                }
            }
            for (final AbstractVariableReference ref : removeInner) {
                changed = true;
                innerMap.remove(ref);
            }
            if (innerMap.isEmpty()) {
                removeOuter.add(entry.getKey());
            }
        }
        for (final AbstractVariableReference ref : removeOuter) {
            changed = true;
            this.map.remove(ref);
        }
        return changed;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ArrayInfo clone() {
        final ArrayInfo clone = new ArrayInfo();
        for (final Map.Entry<AbstractVariableReference, Map<AbstractVariableReference, AbstractVariableReference>> entry : this.map.entrySet()) {
            final Map<AbstractVariableReference, AbstractVariableReference> innerMap = entry.getValue();
            for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> innerEntry : innerMap.entrySet()) {
                clone.add(entry.getKey(), innerEntry.getKey(), innerEntry.getValue());
            }
        }
        return clone;
    }

    /**
     * @param arrayRef the array
     * @param indexRef the index
     * @return if known, the content array[index], null otherwise
     */
    public AbstractVariableReference get(final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef) {
        final Map<AbstractVariableReference, AbstractVariableReference> innerMap = this.map.get(arrayRef);
        if (innerMap != null) {
            return innerMap.get(indexRef);
        }
        return null;
    }


    /**
     * @return the array references for which some information is known
     */
    public Collection<AbstractVariableReference> getArrayRefs() {
        return new LinkedHashSet<>(this.map.keySet());
    }

    /**
     * @return the references that somehow appear (array, index, content).
     */
    public Collection<? extends AbstractVariableReference> getReferences() {
        final Collection<AbstractVariableReference> res = new LinkedHashSet<>();
        res.addAll(this.map.keySet());
        for (final Map<AbstractVariableReference, AbstractVariableReference> value : this.map.values()) {
            res.addAll(value.keySet());
            res.addAll(value.values());
        }
        return res;
    }

    /**
     * Remove all information for the given reference
     * @param ref a reference
     */
    public void remove(final AbstractVariableReference ref) {
        this.clean(Collections.singleton(ref), null);
    }

    /**
     * Rename the given reference and remove information that became useless.
     * @param oldRef the replaced reference
     * @param newRef the replacement reference
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        if (oldRef.equals(newRef)) {
            return;
        }

        for (final Map<AbstractVariableReference, AbstractVariableReference> innerMap : this.map.values()) {
            ArrayInfo.replaceReference(innerMap, oldRef, newRef);
        }

        final Map<AbstractVariableReference, AbstractVariableReference> innerMapOld = this.map.remove(oldRef);
        if (innerMapOld != null && !newRef.isNULLRef()) {
            this.map.put(newRef, innerMapOld);
        }
    }

    /**
     * Rename the given reference and remove information that became useless.
     * @param innerMap the map to work on (index -> content)
     * @param oldRef the replaced reference
     * @param newRef the replacement reference
     */
    private static void replaceReference(final Map<AbstractVariableReference, AbstractVariableReference> innerMap,
        final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef) {
        final AbstractVariableReference oldContent = innerMap.remove(oldRef);
        if (oldContent != null) {
            innerMap.put(newRef, oldContent);
        }
        for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entry : innerMap.entrySet()) {
            if (entry.getValue().equals(oldRef)) {
                entry.setValue(newRef);
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder t = new StringBuilder();
        this.toString(t);
        return t.toString();
    }

    /**
     * Add a nice string representation to the string builder
     * @param t a string builder
     */
    public void toString(final StringBuilder t) {
        for (final Map.Entry<AbstractVariableReference, Map<AbstractVariableReference, AbstractVariableReference>> entry : this.map.entrySet()) {
            for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entryInner : entry.getValue().entrySet()) {
                t.append(entry.getKey());
                t.append("[");
                t.append(entryInner.getKey());
                t.append("] = ");
                t.append(entryInner.getValue());
                t.append("\n");
            }
        }
    }

    /**
     * Remove everything.
     */
    public void clear() {
        this.map.clear();
    }

    /**
     * @return the information as triples
     */
    public Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>> getTriples() {
        final Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>> res =
            new LinkedHashSet<>();
        for (final Map.Entry<AbstractVariableReference, Map<AbstractVariableReference, AbstractVariableReference>> entry : this.map.entrySet()) {
            for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entryInner : entry.getValue().entrySet()) {
                res.add(new Triple<>(entry.getKey(), entryInner.getKey(), entryInner.getValue()));
            }
        }
        return res;
    }

    /**
     * Remove information about array[index] = something
     * @param arrayRef a reference
     * @param indexRef a reference
     */
    public void remove(final AbstractVariableReference arrayRef, final AbstractVariableReference indexRef) {
        final Map<AbstractVariableReference, AbstractVariableReference> innerMap = this.map.get(arrayRef);
        if (innerMap != null) {
            innerMap.remove(indexRef);
            if (innerMap.isEmpty()) {
                this.map.remove(arrayRef);
            }
        }
    }
}
