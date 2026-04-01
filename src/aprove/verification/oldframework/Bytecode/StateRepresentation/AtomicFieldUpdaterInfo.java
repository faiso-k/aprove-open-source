package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Convenience class holding the information about atomic field updaters in a
 * state. These are used in the Java standard API to ensure atomic set and get
 * operations on object instance fields.
 *
 * @author Marc Brockschmidt
 */
public class AtomicFieldUpdaterInfo implements Cloneable {
    /**
     * Class holding the actual data a single field updater needs.
     *
     * @author Marc Brockschmidt
     */
    public static class AtomicFieldUpdaterData {
        /**
         * The type of the instance that is updated.
         */
        private final FuzzyClassType instanceType;

        /**
         * The field name to update.
         */
        private final String fieldName;

        /**
         * The type of the field's value.
         */
        private final FuzzyType fieldType;

        /**
         * Create a fresh data object for a field updater.
         *
         * @param instType the type of the instance that is updated.
         * @param fName the field name to update.
         * @param fType the type of the field's value.
         */
        public AtomicFieldUpdaterData(final FuzzyClassType instType, final String fName, final FuzzyType fType) {
            this.instanceType = instType;
            this.fieldName = fName;
            this.fieldType = fType;
        }

        /**
         * @return the instanceType
         */
        public FuzzyClassType getInstanceType() {
            return this.instanceType;
        }

        /**
         * @return the fieldName
         */
        public String getFieldName() {
            return this.fieldName;
        }

        /**
         * @return the fieldType
         */
        public FuzzyType getFieldType() {
            return this.fieldType;
        }
    }

    /**
     * Map from references to atomic field updaters to the corresponding
     * detail information.
     */
    private LinkedHashMap<AbstractVariableReference, AtomicFieldUpdaterData> refToDataMap;

    /**
     * Creates a new information holder.
     */
    public AtomicFieldUpdaterInfo() {
        this.refToDataMap =
            new LinkedHashMap<AbstractVariableReference, AtomicFieldUpdaterData>();
    }

    /**
     * Returns a deep (!) copy of this {@link AtomicFieldUpdaterInfo} object.
     * @return Deep copy of this object
     */
    @Override
    public AtomicFieldUpdaterInfo clone() {
        final AtomicFieldUpdaterInfo clone = new AtomicFieldUpdaterInfo();

        clone.refToDataMap =
            new LinkedHashMap<AbstractVariableReference, AtomicFieldUpdaterData>();
        for (final Map.Entry<AbstractVariableReference, AtomicFieldUpdaterData> e : this.refToDataMap.entrySet()) {
            clone.refToDataMap.put(e.getKey(), e.getValue());
        }

        return clone;
    }

    /**
     * Remove the variable information for the given reference.
     * @param ref some reference
     */
    public void remove(final AbstractVariableReference ref) {
        this.refToDataMap.remove(ref);
    }

    /**
     * Replace oldRef by newRef
     * @param oldRef a reference
     * @param newRef another reference
     */
    public void replaceReference(final AbstractVariableReference oldRef,
            final AbstractVariableReference newRef) {
        if (this.refToDataMap.containsKey(oldRef)) {
            final AtomicFieldUpdaterData oldVal = this.refToDataMap.get(oldRef);
            this.refToDataMap.remove(oldRef);
            this.refToDataMap.put(newRef, oldVal);
        }

    }

    /**
     * Note a new updater.
     *
     * @param ref the reference pointing to the updater instance.
     * @param instType the type of the instance that is updated.
     * @param fName the field name to update.
     * @param fType the type of the field's value.
     */
    public void addUpdater(final AbstractVariableReference ref, final FuzzyClassType instType, final String fName, final FuzzyType fType) {
        this.refToDataMap.put(ref,
                new AtomicFieldUpdaterData(instType, fName, fType));
    }

    /**
     * @param updaterRef some abstract reference
     * @return the information associated with that reference.
     */
    public AtomicFieldUpdaterData get(final AbstractVariableReference updaterRef) {
        return this.refToDataMap.get(updaterRef);
    }
}
