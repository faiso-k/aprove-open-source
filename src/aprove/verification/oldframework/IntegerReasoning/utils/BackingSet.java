package aprove.verification.oldframework.IntegerReasoning.utils;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A set of relations that is used solely as a backing set for
 * {@link TraditionalIntegerInterface}. The only advantage over a normal Set<>
 * is that this set tries to keep redundant relations as few as possible and
 * also tries to detect inconsistencies when adding new relations.
 *
 * We chose not to implement Collection<Relation> or Set<Relation> since those
 * interfaces are very bloated and we only need very little functionality for
 * the intended use in RelationSetIntegerInterface.
 *
 * @author Alexander Weinert
 */
public class BackingSet implements Iterable<IntegerRelation> {
    /** The actual, very stupid set of relations */
    private final Map<Pair<FunctionalIntegerExpression, FunctionalIntegerExpression>, IntegerRelation> internalSet;
    /** Holds for each variable the relations it appears in */
    private final Map<IntegerVariable, Collection<IntegerRelation>> containingRelations;

    /**
     * Creates an empty BackingSet
     */
    public BackingSet() {
        this.internalSet = new HashMap<>();
        this.containingRelations = new HashMap<>();
    }

    /**
     * Creates a copy of the given BackingSet
     * @param other Some other BackingSet
     */
    public BackingSet(final BackingSet other) {
        this.internalSet = new HashMap<>(other.internalSet);
        this.containingRelations = new HashMap<>(other.containingRelations);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.internalSet == null) ? 0 : this.internalSet.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof BackingSet)) {
            return false;
        }
        final BackingSet other = (BackingSet) obj;
        if (this.internalSet == null) {
            if (other.internalSet != null) {
                return false;
            }
        } else if (!this.internalSet.equals(other.internalSet)) {
            return false;
        }
        return true;
    }

    /**
     * Prior to adding the new relation we check if there is some other
     * relation that either subsumes or contradicts the new relation.
     * @param relation Some relation
     * @return True if the relation was actually added to the set
     * @throws IllegalStateException If the new relation contradicts some
     *  already known relation
     */
    public boolean add(final IntegerRelation relation) {

        final FunctionalIntegerExpression lhsExpression = relation.getLhs();
        final FunctionalIntegerExpression rhsExpression = relation.getRhs();

        final Pair<FunctionalIntegerExpression, FunctionalIntegerExpression> key = new Pair<>(lhsExpression, rhsExpression);
        final Pair<FunctionalIntegerExpression, FunctionalIntegerExpression> mirroredKey = new Pair<>(rhsExpression, lhsExpression);

        final Pair<FunctionalIntegerExpression, FunctionalIntegerExpression> existingKey;
        if (this.internalSet.containsKey(key)) {
            existingKey = key;
        } else if (this.internalSet.containsKey(mirroredKey)) {
            existingKey = mirroredKey;
        } else {
            existingKey = null;
        }

        final IntegerRelation addedRelation;
        if (existingKey == null) {
            addedRelation = relation;
            this.internalSet.put(key, relation);
        } else {
            final IntegerRelation existingRelation = this.internalSet.get(existingKey);
            addedRelation = this.intersectRelations(existingRelation, relation);
            this.internalSet.remove(existingKey);
            this.internalSet.put(key, addedRelation);
            for (final IntegerVariable reference : existingRelation.getVariables()) {
                this.containingRelations.get(reference).remove(existingRelation);
            }
        }

        for (final IntegerVariable reference : addedRelation.getVariables()) {
            if (!this.containingRelations.containsKey(reference)) {
                this.containingRelations.put(reference, new LinkedList<IntegerRelation>());
            }
            this.containingRelations.get(reference).add(addedRelation);
        }

        return true;
    }

    private IntegerRelation intersectRelations(final IntegerRelation knownRelation, final IntegerRelation newRelation) {
        final IntegerRelationType knownRelationType = knownRelation.getRelationType();
        final IntegerRelationType newRelationType = newRelation.getRelationType();
        IntegerRelationType intersectedIntRelType = null;
        if (
            knownRelation.getLhs().equals(newRelation.getLhs()) && knownRelation.getRhs().equals(newRelation.getRhs())
        ) {
            intersectedIntRelType = knownRelationType.intersect(newRelationType);
        } else if (
            knownRelation.getLhs().equals(newRelation.getRhs())
            && knownRelation.getRhs().equals(newRelation.getLhs())
        ) {
            intersectedIntRelType = knownRelationType.intersect(newRelationType.mirror());
        } else {
            return null;
        }
        if (intersectedIntRelType == null) {
            throw new IllegalStateException();
        }
        return new PlainIntegerRelation(intersectedIntRelType, knownRelation.getLhs(), knownRelation.getRhs());

    }

    /**
     * The order of lhs and rhs is more or less irrelevant, since
     *  getRelation(lhs, rhs) == getRelation(rhs, lhs).mirror()
     * @param lhs An Expression
     * @param rhs Another Expression
     * @return The relation the two expressions are in, if such a relation is
     *  part of the RelationSet. Null if no relation can be found
     */
    public IntegerRelationType getRelation(FunctionalIntegerExpression lhs, FunctionalIntegerExpression rhs) {
        final IntegerRelation relevantRelation = this.getStoredRelation(lhs, rhs);
        if (relevantRelation == null) {
            // No relevant relation was found
            return null;
        } else if (relevantRelation.getLhs().equals(lhs)) {
            /* The known relation is in the same orientation as the given lhs,
             * we can just return its type */
            return relevantRelation.getRelationType();
        } else {
            /* We know that the relevantRelation relates lhs and rhs. Since its
             * not in the given orientation, it must be mirrored, so we can
             * simply mirror its RelationType */
            return relevantRelation.getRelationType().mirror();
        }
    }

    /**
     * @param lhs Some LLVMExpression
     * @param rhs Some LLVMExpression
     * @return A Relation rel which either has (rel.lhs.equals(lhs) and
     *  rel.rhs.equals(rhs)) or (rel.lhs.equals(rhs) and rel.rhs.equals(lhs))
     */
    private IntegerRelation getStoredRelation(FunctionalIntegerExpression lhs, FunctionalIntegerExpression rhs) {
        for (final IntegerRelation relation : this) {
            final FunctionalIntegerExpression currentLhs = relation.getLhs();
            final FunctionalIntegerExpression currentRhs = relation.getRhs();
            if (currentLhs.equals(lhs) && currentRhs.equals(rhs)) {
                return relation;
            } else if (currentRhs.equals(lhs) && currentLhs.equals(rhs)) {
                return relation;
            }
        }
        return null;
    }

//    /**
//     * A solution of a relation set is defined as an assignment of values to
//     * the variables of its relations, such that all relations hold. To merge
//     * the solutions of two sets we intersect the sets themselves, thus
//     * removing constraints and adding solutions.
//     * This might also introduce new solutions.
//     * @param other Some other relation set
//     * @return A new relation set that describes a set of solutions ret, such
//     *  that each solution for one of this or other is also a solution of the
//     *  return value.
//     */
//    public BackingSet mergeSolutions(final BackingSet other) {
//        final BackingSet returnValue = new BackingSet();
//        for (final IntegerRelation thisRelation : this) {
//            for (final IntegerRelation otherRelation : other) {
//                if (thisRelation.canRepresentStrictestSubsumingRelation(otherRelation)) {
//                    final IntegerRelation newRelation = thisRelation.getStrictestSubsumingRelation(otherRelation);
//                    returnValue.add(newRelation);
//                }
//            }
//        }
//        return returnValue;
//    }

    /**
     * Returns a new BackingSetInterface where every occurrence of a reference
     * has been replaced using the given renaming. The existing object is not
     * modified.
     * @param renaming Some renaming
     * @return A new BackingSet with the given renaming applied
     */
    public BackingSet rename(final Map<IntegerVariable, IntegerVariable> renaming) {
        final BackingSet returnValue = new BackingSet();
        for (final IntegerRelation rel : this.internalSet.values()) {
            returnValue.add(rel.applySubstitution(renaming));
        }
        return returnValue;
    }

    public Collection<IntegerRelation> getRelationsContainingOneOf(final Collection<IntegerVariable> variables) {
        final Collection<IntegerRelation> returnValue = new HashSet<>();
        for (final IntegerVariable variable : variables) {
            if (this.containingRelations.containsKey(variable)) {
                returnValue.addAll(this.containingRelations.get(variable));
            }
        }
        return returnValue;
    }

    @Override
    public Iterator<IntegerRelation> iterator() {
        return this.internalSet.values().iterator();
    }

    @Override
    public String toString() {
        return this.internalSet.values().toString();
    }

//    public int computeMaximalNumberOfVariableOccurrences() {
//        int curMax = 0;
//        for (final IntegerRelation relation : this.internalSet.values()) {
//            final int curNumOcc = relation.getNumberOfVarOccs();
//            curMax = Math.max(curMax, curNumOcc);
//        }
//        return curMax;
//    }

    public Iterable<IntegerRelation> getEquations() {
        final Collection<IntegerRelation> returnValue = new LinkedList<>();
        for (final IntegerRelation relation : this.internalSet.values()) {
            if (relation.getRelationType().equals(IntegerRelationType.EQ)) {
                returnValue.add(relation);
            }
        }
        return returnValue;
    }

//    public BigInteger computeHighestAbsoluteFactor() {
//        BigInteger res = BigInteger.ONE;
//        for (final IntegerRelation rel : this) {
//            res = res.max(rel.computeHighestAbsoluteFactor());
//        }
//        return res;
//    }

    public BackingSet getRelationsWithoutUndirectedInequalities() {
        final BackingSet returnValue = new BackingSet();

        for (final IntegerRelation relation : this.internalSet.values()) {
            if (!relation.getRelationType().equals(IntegerRelationType.NE)) {
                returnValue.add(relation);
            }
        }
        return returnValue;
    }

    public void remove(final IntegerRelation relation) {
        for (final IntegerVariable varRef : relation.getVariables()) {
            this.containingRelations.get(varRef).remove(relation);
        }
        this.internalSet.remove(new Pair<>(relation.getLhs(), relation.getRhs()));
    }

}
