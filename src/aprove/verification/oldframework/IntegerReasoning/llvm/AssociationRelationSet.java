package aprove.verification.oldframework.IntegerReasoning.llvm;


public class AssociationRelationSet {//extends IntegerRelationSet {
//    private final Pair<LLVMHeuristicVariable, Integer> association;
//
//    public static Collection<IntegerRelationSet> fromAssociations(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        final Map<LLVMHeuristicVariable, Integer> associations,
//        final Map<LLVMHeuristicVariable, BigInteger> associationOffsets)
//    {
//        final Collection<IntegerRelationSet> returnValue = new LinkedList<>();
//        for (final Map.Entry<LLVMHeuristicVariable, Integer> association : associations.entrySet()) {
//            returnValue.add(new AssociationRelationSet(allocations, associations, association.getKey(), association
//                .getValue()));
//        }
//        return returnValue;
//    }
//
//    public AssociationRelationSet(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        final Map<LLVMHeuristicVariable, Integer> associations,
//        final LLVMHeuristicVariable associatedReference,
//        final Integer index)
//    {
//        super(AssociationRelationSet.createRelations(allocations, associations, associatedReference, index));
//        this.association = new Pair<>(associatedReference, index);
//    }
//
//    private static Set<LLVMRelation> createRelations(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations,
//        final Map<LLVMHeuristicVariable, Integer> associations,
//        final LLVMHeuristicVariable associatedReference,
//        final Integer index)
//    {
//        final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> allocation = allocations.get(index);
//        final Set<LLVMRelation> returnValue = new HashSet<>();
//        returnValue.add(new LLVMRelation(LLVMHeuristicRelationType.LE, allocation.x, associatedReference));
//        returnValue.add(new LLVMRelation(LLVMHeuristicRelationType.LE, associatedReference, allocation.y));
//
//        for (final Map.Entry<LLVMHeuristicVariable, Integer> association : associations.entrySet()) {
//            if (association.getValue() == index) {
//                continue;
//            }
//            returnValue.add(new LLVMRelation(LLVMHeuristicRelationType.NE, associatedReference, association.getKey()));
//        }
//
//        return returnValue;
//    }
//
//    Pair<LLVMHeuristicVariable, Integer> getAssociation() {
//        return this.association;
//    }
}
