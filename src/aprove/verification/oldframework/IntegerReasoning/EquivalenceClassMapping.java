package aprove.verification.oldframework.IntegerReasoning;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A state holds (among other things) mappings from variable references
 * to abstract values held by these variables. We may know that different
 * references actually point to the same value. All references that point
 * to the same value then form an equivalence class.
 * When merging two states, we consolidate these references into a single
 * reference in the resulting state. For this, we need a mapping from
 * equivalence classes to the references representing the class in the merged
 * state. An EquivalenceClassMapping encapsulates this mapping.
 *
 * @param <Reference> The type of references to variables used in the states
 * @author Alexander Weinert
 */
public class EquivalenceClassMapping<Reference> {
    /** Maps references from the left hand state to the references in the merged state */
    private final HashMap<Reference, Reference> lhsRenaming;
    /** Maps references from the right hand state to the references in the merged state */
    private final HashMap<Reference, Reference> rhsRenaming;
    /** Maps equivalence classes in the left hand state to the references in the merged state */
    private final BidirectionalMap<Set<Reference>, Reference> lhsClassMapping;
    /** Maps equivalence classes in the right hand state to the references in the merged state */
    private final BidirectionalMap<Set<Reference>, Reference> rhsClassMapping;

    /**
     * Creates a new EquivalenceClassMapping without entries
     */
    public EquivalenceClassMapping() {
        this.lhsRenaming = new HashMap<>();
        this.rhsRenaming = new HashMap<>();
        this.lhsClassMapping = new BidirectionalMap<>();
        this.rhsClassMapping = new BidirectionalMap<>();
    }

    /**
     * Note that this class stores a copy of the mapping internally, so
     * subsequent changes to mapping do not affect the behavior of this
     * class.
     * @param mapping The mapping with which to initialize this EquivalenceClassMapping
     */
    public EquivalenceClassMapping(final Map<Pair<Set<Reference>, Set<Reference>>, Reference> mapping) {
        this();
        for (final Map.Entry<Pair<Set<Reference>, Set<Reference>>, Reference> mapEntry : mapping.entrySet()) {
            final Pair<Set<Reference>, Set<Reference>> equivalenceClasses = mapEntry.getKey();
            final Set<Reference> lhsEquivalenceClass = equivalenceClasses.x;
            final Set<Reference> rhsEquivalenceClass = equivalenceClasses.y;
            final Reference mappedToReference = mapEntry.getValue();

            this.lhsClassMapping.putLR(lhsEquivalenceClass, mappedToReference);
            this.rhsClassMapping.putLR(rhsEquivalenceClass, mappedToReference);

            for (final Reference lhsReference : lhsEquivalenceClass) {
                this.lhsRenaming.put(lhsReference, mappedToReference);
            }

            for (final Reference rhsReference : rhsEquivalenceClass) {
                this.rhsRenaming.put(rhsReference, mappedToReference);
            }
        }
    }

    /**
     * @param lhsReference A reference in the left hand state
     * @return The reference in the merged state that the given reference
     *  shall be mapped to
     */
    public Reference getRenamedReferenceFromLhs(final Reference lhsReference) {
        return this.lhsRenaming.get(lhsReference);
    }

    /**
     * @param rhsReference A reference in the right hand state
     * @return The reference in the merged state that the given reference
     *  shall be mapped to
     */
    public Reference getRenamedReferenceFromRhs(final Reference rhsReference) {
        return this.rhsRenaming.get(rhsReference);
    }

    /**
     * @param lhsReference A reference in the left hand state
     * @return The equivalence class of the given reference in the left hand
     *  state
     * @throws IllegalArgumentException If the given reference is not part of
     *  any equivalence class in the left hand state
     */
    public Set<Reference> getLhsEquivalenceClass(final Reference lhsReference) {
        for (final Set<Reference> equivalenceClass : this.lhsClassMapping.keySetLR()) {
            if (equivalenceClass.contains(lhsReference)) {
                return new HashSet<>(equivalenceClass);
            }
        }
        throw new IllegalArgumentException("lhsReference must be contained in some equivalence class");
    }

    /**
     * @param rhsReference A reference in the right hand state
     * @return The equivalence class of the given reference in the left hand
     *  state
     * @throws IllegalArgumentException If the given reference is not part of
     *  any equivalence class in the right hand state
     */
    public Set<Reference> getRhsEquivalenceClass(final Reference rhsReference) {
        for (final Set<Reference> equivalenceClass : this.rhsClassMapping.keySetLR()) {
            if (equivalenceClass.contains(rhsReference)) {
                return new HashSet<>(equivalenceClass);
            }
        }
        throw new IllegalArgumentException("rhsReference must be contained in some equivalence class");
    }

    /**
     * @return A mapping from references in the left hand state to their
     *  renamed version in the merged state
     */
    public Map<Reference, Reference> getLhsRenaming() {
        return new HashMap<>(this.lhsRenaming);
    }

    /**
     * @return A mapping from references in the right hand state to their
     *  renamed version in the merged state
     */
    public Map<Reference, Reference> getRhsRenaming() {
        return new HashMap<>(this.rhsRenaming);
    }
}
