package aprove.verification.oldframework.IntegerReasoning.relationset;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

public class RelationSetIntegerInterface implements IntegerState {

    private final BackingSet backingSet;

    public RelationSetIntegerInterface() {
        this.backingSet = new BackingSet();
    }

    private RelationSetIntegerInterface(final BackingSet backingSet) {
        this.backingSet = backingSet;
    }

    private RelationSetIntegerInterface(final RelationSetIntegerInterface other) {
        this.backingSet = new BackingSet(other.backingSet);
    }

    @Override
    public IntegerState addRelation(final IntegerRelation relation, Abortion aborter) {
        final RelationSetIntegerInterface returnValue = new RelationSetIntegerInterface(this);
        returnValue.addRelationMutate(relation);
        return returnValue;
    }

    @Override
    public IntegerState addRelationSet(final Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        final RelationSetIntegerInterface returnValue = new RelationSetIntegerInterface(this);
        for (final IntegerRelation relation : relations) {
            returnValue.addRelationMutate(relation);
        }
        return returnValue;
    }

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(final IntegerRelation relation, Abortion aborter) {
        final FunctionalIntegerExpression lhs = relation.getLhs();
        final FunctionalIntegerExpression rhs = relation.getRhs();
        final IntegerRelationType relationType = relation.getRelationType();
        final IntegerRelationType knownRelation = this.backingSet.getRelation(lhs, rhs);
        if (knownRelation == null) {
            // We have no information at all about the relation between the two expressions
            return new Pair<Boolean, IntegerState>(false, this);
        } else if (knownRelation.contradicts(relationType)) {
            // The queried relation contradicts something we already know
            return new Pair<Boolean, IntegerState>(false, this);
        } else if (knownRelation.subSumes(relationType)) {
            // We know a relation that implies the queried relation
            return new Pair<Boolean, IntegerState>(true, this);
        } else {
            /* We know of a relation between the two expressions, but it is
             * weaker than the queried relation */
            return new Pair<Boolean, IntegerState>(false, this);
        }
    }

//    @Override
//    public LLVMHeuristicVariable findReference(final FunctionalIntegerExpression expression) {
//        for (final IntegerRelation relation : this.backingSet) {
//            final LLVMHeuristicVariable foundReference = this.findReference(relation, expression);
//            if (foundReference != null) {
//                return foundReference;
//            }
//        }
//        return null;
//    }

//    /**
//     * @param relation Some relation
//     * @param expression Some expression
//     * @return x, if relation is of the form x = expression or expression = x.
//     *  Null otherwise
//     */
//    public LLVMHeuristicVariable findReference(final IntegerRelation relation, final FunctionalIntegerExpression expression) {
//        if (!relation.getRelationType().equals(LLVMHeuristicRelationType.EQ)) {
//            return null;
//        }
//        final FunctionalIntegerExpression lhs = relation.getLhs();
//        final FunctionalIntegerExpression rhs = relation.getRhs();
//        if (lhs.equals(expression)) {
//            if (rhs instanceof LLVMHeuristicVariable) {
//                return (LLVMHeuristicVariable) rhs;
//            }
//        } else if (rhs.equals(expression)) {
//            if (lhs instanceof LLVMHeuristicVariable) {
//                return (LLVMHeuristicVariable) lhs;
//            }
//        }
//        return null;
//    }

//    @Override
//    public Merger<IntegerState, LLVMHeuristicVariable> getMerger() {
//        return new Merger<IntegerState, LLVMHeuristicVariable>() {
//
//            @Override
//            public IntegerState merge(
//                final IntegerState lhsState,
//                final IntegerState rhsState,
//                final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//            {
//                if (!(lhsState instanceof RelationSetIntegerInterface)) {
//                    throw new IllegalArgumentException("lhsState must be of type RelationSetIntegerInterface");
//                }
//                if (!(rhsState instanceof RelationSetIntegerInterface)) {
//                    throw new IllegalArgumentException("rhsState must be of type RelationSetIntegerInterface");
//                }
//
//                final RelationSetIntegerInterface lhsSetState = (RelationSetIntegerInterface) lhsState;
//                final RelationSetIntegerInterface rhsSetState = (RelationSetIntegerInterface) rhsState;
//
//                final BackingSet mergedSet = lhsSetState.backingSet.mergeSolutions(rhsSetState.backingSet);
//
//                return new RelationSetIntegerInterface(mergedSet);
//            }
//        };
//    }

    @Override
    public String toDOTString() {
        return "RelationSetIntegerInterface: " + this.backingSet.toString();
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("backing_set", JSONExportUtil.toJSON(this.backingSet));
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        final IntegerRelationSet returnValue = new IntegerRelationSet();
        /* We need this foreach-workaround instead of returnValue.addAll,
         * since addAll demands a Collection<> for whatever reason.
         * However, Collection<> is a very bloated interface and we want
         * to keep BackingSet as small as possible */
        for (final IntegerRelation relation : this.backingSet) {
            returnValue.add(relation);
        }
        return returnValue;
    }

    private boolean addRelationMutate(final IntegerRelation relation) {
        return this.backingSet.add(relation);
    }

}
