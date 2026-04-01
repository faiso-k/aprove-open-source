package aprove.verification.oldframework.IntegerReasoning.llvm;


class LLVMIntegerStateMerger {//implements Merger<IntegerState, LLVMHeuristicVariable> {
//
//    private final boolean useSmt;
//
//    public LLVMIntegerStateMerger(final boolean useSmt) {
//        this.useSmt = useSmt;
//    }
//
//    @Override
//    public IntegerState merge(
//        final IntegerState lhsState,
//        final IntegerState rhsState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        assert lhsState instanceof LLVMIntegerState : "lhsState must be instance of LLVMIntegerState";
//        assert rhsState instanceof LLVMIntegerState : "lhsState must be instance of LLVMIntegerState";
//        final LLVMMockState lhsMockState = ((LLVMIntegerState) lhsState).getState();
//        final LLVMMockState rhsMockState = ((LLVMIntegerState) rhsState).getState();
//
//        final LLVMMockState mergedState = this.mergeMockStates(lhsMockState, rhsMockState, equivalenceClassMapping);
//
//        // We set useCache to true since this makes reasoning mightier. Also, before clients use
//        // the integer state they should set the useCache-flag themselves, if they care about it
//        return new LLVMIntegerState(mergedState, true);
//    }
//
//    public LLVMIntegerStateMerger setUseSmt(final boolean useSmt) {
//        return new LLVMIntegerStateMerger(useSmt);
//    }
//
//    private LLVMMockState mergeMockStates(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        final ImmutableMap<LLVMHeuristicVariable, LLVMValue> mergedValues =
//            this.mergeValues(lhsMockState, rhsMockState, equivalenceClassMapping);
//        final ImmutableList<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> mergedAllocations =
//            this.mergeAllocations(lhsMockState, rhsMockState, equivalenceClassMapping);
//        final ImmutableMap<LLVMHeuristicVariable, Integer> mergedAssociations =
//            this.mergeAssociations(lhsMockState, rhsMockState, equivalenceClassMapping, mergedAllocations);
//        final ImmutableMap<LLVMHeuristicVariable, BigInteger> mergedAssociationOffsets =
//            this.mergeAssociationOffsets(lhsMockState, rhsMockState, equivalenceClassMapping);
//        final ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> mergedUnequalCache =
//            this.mergeUnequalCache(lhsMockState, rhsMockState, equivalenceClassMapping);
//        final ImmutableSet<LLVMRelation> mergedRelations =
//            this.mergeRelations(lhsMockState, rhsMockState, equivalenceClassMapping);
//
//        return new LLVMMockState(
//            mergedValues,
//            mergedAllocations,
//            mergedAssociations,
//            mergedAssociationOffsets,
//            mergedUnequalCache,
//            mergedRelations);
//    }
//
//    private ImmutableMap<LLVMHeuristicVariable, LLVMValue> mergeValues(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        final Map<LLVMHeuristicVariable, LLVMValue> lhsValues = lhsMockState.getValues();
//        final Map<LLVMHeuristicVariable, LLVMValue> rhsValues = rhsMockState.getValues();
//
//        final Map<LLVMHeuristicVariable, Collection<LLVMValue>> lhsRenamed = new HashMap<>();
//        for (final Map.Entry<LLVMHeuristicVariable, LLVMValue> lhsEntry : lhsValues.entrySet()) {
//            final LLVMHeuristicVariable renamedLhsEntry = equivalenceClassMapping.getRenamedReferenceFromLhs(lhsEntry.getKey());
//            if (!lhsRenamed.containsKey(renamedLhsEntry)) {
//                lhsRenamed.put(renamedLhsEntry, new HashSet<LLVMValue>());
//            }
//            lhsRenamed.get(renamedLhsEntry).add(lhsEntry.getValue());
//        }
//
//        final Map<LLVMHeuristicVariable, Collection<LLVMValue>> rhsRenamed = new HashMap<>();
//        for (final Map.Entry<LLVMHeuristicVariable, LLVMValue> rhsEntry : rhsValues.entrySet()) {
//            final LLVMHeuristicVariable renamedRhsEntry = equivalenceClassMapping.getRenamedReferenceFromRhs(rhsEntry.getKey());
//            if (!rhsRenamed.containsKey(renamedRhsEntry)) {
//                rhsRenamed.put(renamedRhsEntry, new HashSet<LLVMValue>());
//            }
//            rhsRenamed.get(renamedRhsEntry).add(rhsEntry.getValue());
//        }
//
//        final Map<LLVMHeuristicVariable, Collection<LLVMValue>> mergedValues = new HashMap<>(lhsRenamed);
//        for (final Map.Entry<LLVMHeuristicVariable, Collection<LLVMValue>> rhsRenamedEntry : rhsRenamed.entrySet()) {
//            if (mergedValues.containsKey(rhsRenamedEntry.getKey())) {
//                mergedValues.get(rhsRenamedEntry).addAll(rhsRenamedEntry.getValue());
//            } else {
//                mergedValues.put(rhsRenamedEntry.getKey(), rhsRenamedEntry.getValue());
//            }
//        }
//
//        final Map<LLVMHeuristicVariable, LLVMValue> returnValue = new HashMap<>();
//        for (final Map.Entry<LLVMHeuristicVariable, Collection<LLVMValue>> mergedValue : mergedValues.entrySet()) {
//            final Iterator<LLVMValue> valueIterator = mergedValue.getValue().iterator();
//            AbstractNumber mergeResult = valueIterator.next().getThisAsAbstractInt();
//            while (valueIterator.hasNext()) {
//                final AbstractNumber currentValue = valueIterator.next().getThisAsAbstractInt();
//                final IntegerType resultType;
//                if (mergeResult.getThisAsAbstractInt().isPositive() && currentValue.getThisAsAbstractInt().isPositive())
//                {
//                    resultType = IntegerType.UNBOUND_POSITIVE;
//                } else if (mergeResult.getThisAsAbstractInt().isNonNegative()
//                    && currentValue.getThisAsAbstractInt().isNonNegative())
//                {
//                    resultType = IntegerType.UNBOUND_NON_NEGATIVE;
//                } else {
//                    resultType = IntegerType.UNBOUND;
//                }
//                mergeResult =
//                    mergeResult.getThisAsAbstractInt().merge(currentValue, true, resultType).getMergedVariable();
//            }
//        }
//
//        return ImmutableCreator.create(returnValue);
//    }
//
//    private ImmutableList<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> mergeAllocations(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> returnValue = new LinkedList<>();
//
//        for (final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> lhsAlloc : lhsMockState.getAllocations()) {
//            final LLVMHeuristicVariable renamedLowerBound = equivalenceClassMapping.getRenamedReferenceFromLhs(lhsAlloc.x);
//            final LLVMHeuristicVariable renamedUpperBound = equivalenceClassMapping.getRenamedReferenceFromLhs(lhsAlloc.y);
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> renamedAllocation =
//                new ImmutablePair<>(renamedLowerBound, renamedUpperBound);
//
//            if (!returnValue.contains(renamedAllocation)) {
//                returnValue.add(renamedAllocation);
//            }
//        }
//
//        for (final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> rhsAlloc : rhsMockState.getAllocations()) {
//            final LLVMHeuristicVariable renamedLowerBound = equivalenceClassMapping.getRenamedReferenceFromRhs(rhsAlloc.x);
//            final LLVMHeuristicVariable renamedUpperBound = equivalenceClassMapping.getRenamedReferenceFromRhs(rhsAlloc.y);
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> renamedAllocation =
//                new ImmutablePair<>(renamedLowerBound, renamedUpperBound);
//
//            if (!returnValue.contains(renamedAllocation)) {
//                returnValue.add(renamedAllocation);
//            }
//        }
//
//        return ImmutableCreator.create(returnValue);
//    }
//
//    private ImmutableMap<LLVMHeuristicVariable, Integer> mergeAssociations(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping,
//        final List<ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable>> mergedAllocations)
//    {
//        final Map<LLVMHeuristicVariable, Integer> returnValue = new HashMap<>();
//        for (final Map.Entry<LLVMHeuristicVariable, Integer> lhsAssoc : lhsMockState.getAssociations().entrySet()) {
//            final LLVMHeuristicVariable renamedRef = equivalenceClassMapping.getRenamedReferenceFromLhs(lhsAssoc.getKey());
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> originalAllocation =
//                lhsMockState.getAllocations().get(lhsAssoc.getValue());
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> renamedAllocation =
//                new ImmutablePair<>(
//                    equivalenceClassMapping.getRenamedReferenceFromLhs(originalAllocation.x),
//                    equivalenceClassMapping.getRenamedReferenceFromLhs(originalAllocation.y));
//
//            assert mergedAllocations.contains(renamedAllocation);
//            final int allocationIndex = mergedAllocations.indexOf(renamedAllocation);
//            returnValue.put(renamedRef, allocationIndex);
//        }
//        for (final Map.Entry<LLVMHeuristicVariable, Integer> rhsAssoc : rhsMockState.getAssociations().entrySet()) {
//            final LLVMHeuristicVariable renamedRef = equivalenceClassMapping.getRenamedReferenceFromRhs(rhsAssoc.getKey());
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> originalAllocation =
//                rhsMockState.getAllocations().get(rhsAssoc.getValue());
//            final ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> renamedAllocation =
//                new ImmutablePair<>(
//                    equivalenceClassMapping.getRenamedReferenceFromRhs(originalAllocation.x),
//                    equivalenceClassMapping.getRenamedReferenceFromRhs(originalAllocation.y));
//
//            assert mergedAllocations.contains(renamedAllocation);
//            final int allocationIndex = mergedAllocations.indexOf(renamedAllocation);
//            returnValue.put(renamedRef, allocationIndex);
//        }
//        return ImmutableCreator.create(returnValue);
//    }
//
//    private ImmutableMap<LLVMHeuristicVariable, BigInteger> mergeAssociationOffsets(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        final Map<LLVMHeuristicVariable, BigInteger> returnValue = new HashMap<>();
//        for (final Map.Entry<LLVMHeuristicVariable, BigInteger> lhsAssocOffset : lhsMockState
//            .getAssociationOffsets()
//            .entrySet())
//        {
//            final LLVMHeuristicVariable renamedReference =
//                equivalenceClassMapping.getRenamedReferenceFromLhs(lhsAssocOffset.getKey());
//            final BigInteger newAssocOffset;
//            if (returnValue.containsKey(renamedReference)) {
//                newAssocOffset = returnValue.get(renamedReference).max(lhsAssocOffset.getValue());
//            } else {
//                newAssocOffset = lhsAssocOffset.getValue();
//            }
//            returnValue.put(renamedReference, newAssocOffset);
//        }
//
//        for (final Map.Entry<LLVMHeuristicVariable, BigInteger> rhsAssocOffset : rhsMockState
//            .getAssociationOffsets()
//            .entrySet())
//        {
//            final LLVMHeuristicVariable renamedReference =
//                equivalenceClassMapping.getRenamedReferenceFromRhs(rhsAssocOffset.getKey());
//            final BigInteger newAssocOffset;
//            if (returnValue.containsKey(renamedReference)) {
//                newAssocOffset = returnValue.get(renamedReference).max(rhsAssocOffset.getValue());
//            } else {
//                newAssocOffset = rhsAssocOffset.getValue();
//            }
//            returnValue.put(renamedReference, newAssocOffset);
//        }
//        return ImmutableCreator.create(returnValue);
//    }
//
//    private ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> mergeUnequalCache(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        final Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> returnValue = new HashSet<>();
//        for (final ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> lhsUnequalEntry : lhsMockState.getUnequalCache()) {
//            final LLVMHeuristicVarRef renamedLhsVarRef =
//                (LLVMHeuristicVarRef) equivalenceClassMapping.getRenamedReferenceFromLhs(lhsUnequalEntry.x);
//            final LLVMHeuristicVarRef renamedRhsVarRef =
//                (LLVMHeuristicVarRef) equivalenceClassMapping.getRenamedReferenceFromLhs(lhsUnequalEntry.y);
//            returnValue.add(new ImmutablePair<>(renamedLhsVarRef, renamedRhsVarRef));
//        }
//        for (final ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> rhsUnequalEntry : rhsMockState.getUnequalCache()) {
//            final LLVMHeuristicVarRef renamedLhsVarRef =
//                (LLVMHeuristicVarRef) equivalenceClassMapping.getRenamedReferenceFromRhs(rhsUnequalEntry.x);
//            final LLVMHeuristicVarRef renamedRhsVarRef =
//                (LLVMHeuristicVarRef) equivalenceClassMapping.getRenamedReferenceFromRhs(rhsUnequalEntry.y);
//            returnValue.add(new ImmutablePair<>(renamedLhsVarRef, renamedRhsVarRef));
//        }
//        return ImmutableCreator.create(returnValue);
//    }
//
//    private ImmutableSet<LLVMRelation> mergeRelations(
//        final LLVMMockState lhsMockState,
//        final LLVMMockState rhsMockState,
//        final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//    {
//        final Set<LLVMRelation> returnValue = new HashSet<>();
//        for (final LLVMRelation lhsRel : lhsMockState.getRelations()) {
//            returnValue.add(lhsRel.applySubstitution(equivalenceClassMapping.getLhsRenaming()));
//        }
//        for (final LLVMRelation rhsRel : rhsMockState.getRelations()) {
//            returnValue.add(rhsRel.applySubstitution(equivalenceClassMapping.getLhsRenaming()));
//        }
//        return ImmutableCreator.create(returnValue);
//    }
}
