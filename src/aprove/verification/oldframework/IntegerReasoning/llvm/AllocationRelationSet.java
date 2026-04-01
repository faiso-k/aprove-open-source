package aprove.verification.oldframework.IntegerReasoning.llvm;


public class AllocationRelationSet {//extends IntegerRelationSet {
//    private final Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> allocation;
//
//    public static Collection<IntegerRelationSet> fromAllocations(
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> allocations)
//    {
//        final Collection<IntegerRelationSet> returnValue = new LinkedList<>();
//        for (final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> allocation : allocations) {
//            returnValue.add(new AllocationRelationSet(allocation.x, allocation.y));
//        }
//        return returnValue;
//    }
//
//    public AllocationRelationSet(final LLVMHeuristicVariable lowerBound, final LLVMHeuristicVariable upperBound) {
//        super(new HashSet<LLVMRelation>(Arrays.asList(new LLVMRelation(LLVMHeuristicRelationType.LE, lowerBound, upperBound))));
//        this.allocation = new Pair<>(lowerBound, upperBound);
//    }
//
//    Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> getAllocation() {
//        return this.allocation;
//    }
}
