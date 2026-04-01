package aprove.verification.oldframework.IntegerReasoning.llvm;


public class LLVMIntegerState {//implements IntegerState {
//
//    private final LLVMMockState state;
//    private final boolean useCache;
//
//    public LLVMIntegerState(final boolean useCache) {
//        this.state = new LLVMMockState();
//        this.useCache = useCache;
//    }
//
//    LLVMIntegerState(final LLVMMockState state, final boolean useCache) {
//        this.state = state;
//        this.useCache = useCache;
//    }
//
//    LLVMMockState getState() {
//        return this.state;
//    }
//
//    public IntegerState setUseCache(final boolean useCache) {
//        return new LLVMIntegerState(this.state, useCache);
//    }
//
//    @Override
//    public IntegerState addRelation(final LLVMRelation relation) {
//        return new LLVMIntegerState(this.state.addRelation(relation), this.useCache);
//    }
//
//    @Override
//    public IntegerState addRelationSet(final Iterable<? extends LLVMRelation> relations) {
//        if (relations instanceof ValueRelationSet) {
//            final Pair<LLVMHeuristicVariable, LLVMValue> value = ((ValueRelationSet) relations).getValue();
//            return new LLVMIntegerState(this.state.setValue(value.x, value.y.getThisAsAbstractInt()), this.useCache);
//        } else if (relations instanceof AllocationRelationSet) {
//            final Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> allocation = ((AllocationRelationSet) relations).getAllocation();
//            return new LLVMIntegerState(this.state.addAllocation(allocation.x, allocation.y), this.useCache);
//        } else if (relations instanceof AssociationRelationSet) {
//            final Pair<LLVMHeuristicVariable, Integer> association = ((AssociationRelationSet) relations).getAssociation();
//            return new LLVMIntegerState(this.state.associateVariable(association.x, association.y), this.useCache);
//        } else if (relations instanceof AssociationOffsetRelationSet) {
//            final Pair<LLVMHeuristicVariable, BigInteger> associationOffset =
//                ((AssociationOffsetRelationSet) relations).getAssociationOffset();
//            return new LLVMIntegerState(
//                this.state.setAssociationOffset(associationOffset.x, associationOffset.y),
//                this.useCache);
//        } else if (relations instanceof UnequalCacheRelationSet) {
//            final Pair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> unequalVars =
//                ((UnequalCacheRelationSet) relations).getUnequalVariables();
//            return new LLVMIntegerState(this.state.registerAsUnequal(unequalVars.x, unequalVars.y), this.useCache);
//        } else {
//            final List<LLVMRelation> newRelations = new LinkedList<>();
//            for (final LLVMRelation relation : relations) {
//                newRelations.add(relation);
//            }
//            return new LLVMIntegerState(this.state.addRelations(newRelations), this.useCache);
//        }
//    }
//
//    @Override
//    public LLVMHeuristicVariable findReference(final LLVMHeuristicTerm expression) {
//        return LLVMExpressionUtils.findReferenceForExpression(
//            this.state.getValues(),
//            new IntegerRelationSet(this.state.getRelations()),
//            expression);
//    }
//
//    @Override
//    public YNM checkRelation(final LLVMRelation relation) {
//        final LLVMParameters params =
//            new LLVMParameters(true, true, true, false, LLVMSMT.HEURISTICS, AbortionFactory.create());
//        return IntegerUtils.truthValueOfRelation(this.state, relation, this.useCache, params);
//    }
//
//    @Override
//    public IntegerRelationSet toRelationSet() {
//        return new IntegerRelationSet(this.state.getRelations());
//    }
//
//    @Override
//    public Merger<IntegerState, LLVMHeuristicVariable> getMerger() {
//        // Use SMTSolver by default here in order to achieve the mightiest possible
//        // inference. If the client cares about the value of this, they will change
//        // it anyways
//        return new LLVMIntegerStateMerger(true);
//    }
//
}
