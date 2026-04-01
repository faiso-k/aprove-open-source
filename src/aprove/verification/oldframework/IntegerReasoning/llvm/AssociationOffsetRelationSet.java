package aprove.verification.oldframework.IntegerReasoning.llvm;


public class AssociationOffsetRelationSet {//extends IntegerRelationSet {
//    private final Pair<LLVMHeuristicVariable, BigInteger> associationOffset;
//
//    public static Collection<IntegerRelationSet> fromAssociationOffsets(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        final Map<LLVMHeuristicVariable, Integer> associations,
//        final Map<LLVMHeuristicVariable, BigInteger> associationOffsets)
//    {
//        final Collection<IntegerRelationSet> returnValue = new LinkedList<>();
//        for (final Map.Entry<LLVMHeuristicVariable, BigInteger> offset : associationOffsets.entrySet()) {
//            returnValue.add(new AssociationOffsetRelationSet(allocations, associations, offset.getKey(), offset
//                .getValue()));
//        }
//        return returnValue;
//    }
//
//    public AssociationOffsetRelationSet(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        final Map<LLVMHeuristicVariable, Integer> associations,
//        final LLVMHeuristicVariable associatedReference,
//        final BigInteger offset)
//    {
//        super(AssociationOffsetRelationSet.createRelations(allocations, associations, associatedReference, offset));
//        this.associationOffset = new Pair<>(associatedReference, offset);
//    }
//
//    private static Set<LLVMRelation> createRelations(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        final Map<LLVMHeuristicVariable, Integer> associations,
//        final LLVMHeuristicVariable associatedReference,
//        final BigInteger offset)
//    {
//        final Integer associationIndex = associations.get(associatedReference);
//
//        if (associationIndex != null) {
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> allocation = allocations.get(associationIndex);
//            final LLVMHeuristicTerm referencePlusOffset =
//                LLVMOperation.create(ArithmeticOperationType.ADD, associatedReference, new LLVMHeuristicConstRef(offset));
//            final LLVMRelation relation = new LLVMRelation(LLVMHeuristicRelationType.LE, referencePlusOffset, allocation.y);
//            return Collections.singleton(relation);
//        } else {
//            return Collections.<LLVMRelation>emptySet();
//        }
//
//    }
//
//    Pair<LLVMHeuristicVariable, BigInteger> getAssociationOffset() {
//        return this.associationOffset;
//    }
}
