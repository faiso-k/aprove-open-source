package aprove.verification.oldframework.IntegerReasoning.llvm;


public class ValueRelationSet {//extends IntegerRelationSet {
//    final Pair<LLVMHeuristicVariable, LLVMValue> value;
//
//    public static Collection<IntegerRelationSet> fromValues(final Map<LLVMHeuristicVariable, LLVMValue> values) {
//        final Collection<IntegerRelationSet> returnValue = new LinkedList<>();
//        for (final Map.Entry<LLVMHeuristicVariable, LLVMValue> valueEntry : values.entrySet()) {
//            returnValue.add(new ValueRelationSet(valueEntry.getKey(), valueEntry.getValue()));
//        }
//        return returnValue;
//    }
//
//    public ValueRelationSet(final LLVMHeuristicVariable ref, final LLVMValue val) {
//        super(ValueRelationSet.convertValueToRelations(ref, val));
//        this.value = new Pair<>(ref, val);
//    }
//
//    private static Set<LLVMRelation> convertValueToRelations(final LLVMHeuristicVariable ref, final LLVMValue val) {
//        final Set<LLVMRelation> returnValue = new HashSet<>();
//        if (!(val instanceof AbstractInt)) {
//            return returnValue;
//        }
//
//        final AbstractInt valAsAbstractInt = (AbstractInt) val;
//        if (valAsAbstractInt.getLower().isFinite()) {
//            final BigInteger lowerBound = valAsAbstractInt.getLower().getConstant();
//            final LLVMHeuristicConstRef lowerBoundRef = new LLVMHeuristicConstRef(lowerBound);
//            returnValue.add(new LLVMRelation(LLVMHeuristicRelationType.LE, lowerBoundRef, ref));
//        }
//        if (valAsAbstractInt.getUpper().isFinite()) {
//            final BigInteger upperBound = valAsAbstractInt.getUpper().getConstant();
//            final LLVMHeuristicConstRef upperBoundRef = new LLVMHeuristicConstRef(upperBound);
//            returnValue.add(new LLVMRelation(LLVMHeuristicRelationType.LE, ref, upperBoundRef));
//        }
//        return returnValue;
//    }
//
//    Pair<LLVMHeuristicVariable, LLVMValue> getValue() {
//        return this.value;
//    }
}
