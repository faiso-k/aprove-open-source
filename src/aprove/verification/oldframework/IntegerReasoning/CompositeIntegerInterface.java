package aprove.verification.oldframework.IntegerReasoning;

import java.util.*;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

public class CompositeIntegerInterface implements IntegerState {

    public static IntegerState build(List<IntegerState> newList) {
        return new CompositeIntegerInterface(new LinkedList<>(newList));
    }

    public static IntegerState buildEmptyInterface() {
        return CompositeIntegerInterface.build(Collections.emptyList());
    }

//    public static IntegerState buildLLVMState(
//        Map<LLVMHeuristicVariable, LLVMValue> values,
//        List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        Map<LLVMHeuristicVariable, Integer> associations,
//        Map<LLVMHeuristicVariable, BigInteger> associationOffsets,
//        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> unequalityCache
//    ) {
//        IntegerState newIntegerState =
//            new CompositeIntegerInterface(
//                Arrays.asList(
//                    new ConstantInterface(),
//                    new EqualSidesInterface(),
//                    new LLVMIntegerState(false)
//                )
//            );
//        for (IntegerRelationSet valueSet : ValueRelationSet.fromValues(values)) {
//            newIntegerState = newIntegerState.addRelationSet(valueSet);
//        }
//        for (IntegerRelationSet allocationSet : AllocationRelationSet.fromAllocations(allocations)) {
//            newIntegerState = newIntegerState.addRelationSet(allocationSet);
//        }
//        for (
//            IntegerRelationSet associationSet :
//                AssociationRelationSet.fromAssociations(allocations, associations, associationOffsets)
//        ) {
//            newIntegerState = newIntegerState.addRelationSet(associationSet);
//        }
//        for (
//            IntegerRelationSet associationOffsetSet :
//                AssociationOffsetRelationSet.fromAssociationOffsets(
//                    allocations,
//                    associations,
//                    associationOffsets
//                )
//        ) {
//            newIntegerState = newIntegerState.addRelationSet(associationOffsetSet);
//        }
//        for (IntegerRelationSet unequalSet : UnequalCacheRelationSet.fromUnequalCache(unequalityCache)) {
//            newIntegerState = newIntegerState.addRelationSet(unequalSet);
//        }
//        return newIntegerState;
//    }

//    private static IntegerState buildLLVMInterface() {
//        final List<IntegerState> backingInterfaces = new LinkedList<>();
//        backingInterfaces.add(new ConstantInterface());
//        backingInterfaces.add(new EqualSidesInterface());
//        backingInterfaces.add(new LLVMIntegerState(true));
//        return new CompositeIntegerInterface(backingInterfaces);
//    }

    private final List<IntegerState> backingInterfaces;

    private CompositeIntegerInterface(List<IntegerState> backingInterfaces) {
        this.backingInterfaces = backingInterfaces;
    }

    @Override
    public IntegerState addRelation(IntegerRelation relation, Abortion aborter) {
        final List<IntegerState> updatedInterfaces = new LinkedList<IntegerState>();
        for (IntegerState backingInterface : this.backingInterfaces) {
            updatedInterfaces.add(backingInterface.addRelation(relation, aborter));
        }
        return new CompositeIntegerInterface(updatedInterfaces);
    }

    @Override
    public IntegerState addRelationSet(Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        final List<IntegerState> updatedInterfaces = new LinkedList<IntegerState>();
        for (IntegerState backingInterface : this.backingInterfaces) {
            updatedInterfaces.add(backingInterface.addRelationSet(relations, aborter));
        }
        return new CompositeIntegerInterface(updatedInterfaces);
    }

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(IntegerRelation relation, Abortion aborter) {
        boolean noAnswer = true;
        List<IntegerState> newList = new ArrayList<IntegerState>();
        for (IntegerState backingInterface : this.backingInterfaces) {
            if (noAnswer) {
                Pair<Boolean, ? extends IntegerState> answer = backingInterface.checkRelation(relation, aborter);
                newList.add(answer.y);
                if (answer.x) {
                    noAnswer = false;
                }
            } else {
                newList.add(backingInterface);
            }
        }
        return new Pair<Boolean, IntegerState>(!noAnswer, CompositeIntegerInterface.build(newList));
    }

//    @Override
//    public LLVMHeuristicVariable findReference(LLVMHeuristicTerm expression) {
//        for (IntegerState backingInterface : this.backingInterfaces) {
//            final LLVMHeuristicVariable foundReference = backingInterface.findReference(expression);
//            if (foundReference != null) {
//                return foundReference;
//            }
//        }
//
//        return null;
//    }

    public List<IntegerState> getCompoundStates() {
        return new LinkedList<IntegerState>(this.backingInterfaces);
    }

//    @Override
//    public Merger<IntegerState, LLVMHeuristicVariable> getMerger() {
//        return new Merger<IntegerState, LLVMHeuristicVariable>() {
//
//            @Override
//            public IntegerState merge(
//                IntegerState lhsState,
//                IntegerState rhsState,
//                EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping
//            ) {
//                if (!(lhsState instanceof CompositeIntegerInterface)) {
//                    return null;
//                }
//                if (!(rhsState instanceof CompositeIntegerInterface)) {
//                    return null;
//                }
//                final List<IntegerState> lhsBacking = ((CompositeIntegerInterface) lhsState).backingInterfaces;
//                final List<IntegerState> rhsBacking = ((CompositeIntegerInterface) rhsState).backingInterfaces;
//                if (lhsBacking.size() != rhsBacking.size()) {
//                    return null;
//                }
//                final List<IntegerState> mergedInterfaces = new LinkedList<>();
//                for (int i = 0; i < lhsBacking.size(); ++i) {
//                    final IntegerState currentLhsBacking = lhsBacking.get(i);
//                    final IntegerState currentRhsBacking = rhsBacking.get(i);
//                    if (!currentLhsBacking.getClass().equals(currentRhsBacking.getClass())) {
//                        return null;
//                    }
//                    final Merger<IntegerState, LLVMHeuristicVariable> merger = currentLhsBacking.getMerger();
//                    final IntegerState mergedInterface =
//                        merger.merge(currentLhsBacking, currentRhsBacking, equivalenceClassMapping);
//                    mergedInterfaces.add(mergedInterface);
//                }
//                return new CompositeIntegerInterface(mergedInterfaces);
//            }
//
//        };
//    }

    @Override
    public String toDOTString() {
        return this.toString().replaceAll("\\", "\\\\");
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("interfaces", JSONExportUtil.toJSON(this.backingInterfaces));
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        final IntegerRelationSet returnValue = new IntegerRelationSet();
        for (IntegerState backingInterface : this.backingInterfaces) {
            returnValue.addAll(backingInterface.toRelationSet());
        }
        return returnValue;
    }

    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder();
        builder.append(this.getClass().getSimpleName());
        builder.append(" consisting of ");
        builder.append(this.backingInterfaces.size());
        builder.append(" backing interfaces:\n");
        for (IntegerState compoundInterface : this.backingInterfaces) {
            builder.append(compoundInterface.toString());
            builder.append('\n');
        }
        return builder.toString();
    }

}
