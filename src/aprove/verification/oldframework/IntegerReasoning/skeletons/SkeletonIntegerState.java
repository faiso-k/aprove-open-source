package aprove.verification.oldframework.IntegerReasoning.skeletons;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * When implementing the {@link IntegerState}, many of the functions are
 * usually implemented in similar ways. For example, addRelation is usually
 * implemented by cloning the current state and then mutating the clone, which
 * is subsequently handed out to the caller.
 *
 * {@link SkeletonIntegerState} tries to reduce boilerplate code by
 * implementing {@link IntegerState} in terms of five more specific
 * methods whose implementation depends strongly on the actual representation
 * of relations.
 *
 * @author Alexander Weinert
 */
public abstract class SkeletonIntegerState implements IntegerState {

    /**
     * A Collection containing all references of all relations that were added
     * to this state.
     */
    private final Collection<IntegerVariable> knownReferences = new HashSet<>();

    @Override
    public IntegerState addRelation(final IntegerRelation relation, Abortion aborter) {
        final SkeletonIntegerState copiedState = this.deepCopy();
        copiedState.knownReferences.addAll(relation.getVariables());
        copiedState.addRelationMutate(relation);
        return copiedState;
    }

    @Override
    public IntegerState addRelationSet(final Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        final SkeletonIntegerState copiedState = this.deepCopy();
        for (final IntegerRelation relation : relations) {
            copiedState.knownReferences.addAll(relation.getVariables());
            copiedState.addRelationMutate(relation);
        }
        return copiedState;
    }

    /**
     * A copy is sufficiently deep if no change to the copied object affects
     * the original object anymore. The returned object has to be completely
     * independent of this object.
     *
     * @return A sufficiently deep copy of this object.
     */
    protected abstract SkeletonIntegerState deepCopy();

    /**
     * Adds the given relation to this state, changing the state in the
     * process. Since {@link IntegerState} is supposed to be immutable,
     * this method is only called on a newly created copy before it is handed
     * out to the client.
     *
     * This method may not be called anymore once the object has been handed
     * to a client to preserve immutability!
     *
     * @param relation Some relation
     */
    protected abstract void addRelationMutate(final IntegerRelation relation);

//    /**
//     * {@inheritDoc}
//     * This skeleton implementation implements a very simple inference of
//     * references, by calling checkRelation.(ref == expr) for each known
//     * reference. This inference is sound, but somewhat slow.
//     *
//     * <em>If possible, this method should be overriden in subclasses in order
//     * to speed up inference</em>
//     */
//    @Override
//    public IntegerVariable findReference(final LLVMHeuristicTerm expression) {
//        if (expression instanceof IntegerVariable) {
//            return (IntegerVariable) expression;
//        }
//        for (final IntegerVariable reference : this.knownReferences) {
//            final IntegerRelation equalityRelation = new IntegerRelation(LLVMHeuristicRelationType.EQ, reference, expression);
//            if (this.checkRelation(equalityRelation) == YNM.YES) {
//                return reference;
//            }
//        }
//
//        return null;
//    }

//    @Override
//    public Merger<IntegerState, IntegerVariable> getMerger() {
//        return new Merger<IntegerState, IntegerVariable>() {
//
//            @Override
//            public IntegerState merge(
//                final IntegerState lhsState,
//                final IntegerState rhsState,
//                final EquivalenceClassMapping<IntegerVariable> equivalenceClassMapping)
//            {
//                if (!(lhsState instanceof SkeletonIntegerState)) {
//                    throw new IllegalArgumentException("lhsState must be a SkeletonIntegerState");
//                }
//                final SkeletonIntegerState lhsSkeletonState = (SkeletonIntegerState) lhsState;
//
//                if (!(rhsState instanceof SkeletonIntegerState)) {
//                    throw new IllegalArgumentException("rhsState must be a SkeletonIntegerState");
//                }
//                final SkeletonIntegerState rhsSkeletonState = (SkeletonIntegerState) rhsState;
//
//                final SkeletonIntegerState clonedLhsState = lhsSkeletonState.deepCopy();
//                clonedLhsState.renameMutate(equivalenceClassMapping.getLhsRenaming());
//
//                final SkeletonIntegerState clonedRhsState = rhsSkeletonState.deepCopy();
//                clonedRhsState.renameMutate(equivalenceClassMapping.getRhsRenaming());
//
//                return clonedLhsState.merge(clonedRhsState);
//            }
//        };
//    }

    /**
     * Renames this IntegerState using the given renaming. Since this mutates
     * the state, this method may only be used internally.
     *
     * @param renaming Some renaming of LLVMReferences
     */
    protected abstract void renameMutate(final Map<IntegerVariable, IntegerVariable> renaming);

    /**
     * @param other Some other IntegerInterface
     * @return A new IntegerInterface that describes the union of states
     * described by this and other.
     */
    protected abstract IntegerState merge(final IntegerState other);
}
