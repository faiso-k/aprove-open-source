package aprove.input.Programs.llvm.internalStructures.instructions;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A store instruction.
 * TODO: Add volatile parameter and check it (when storing a trap value, this is undefined behavior).
 * @author Janine Repke, CryingShadow, Jera Hensel
 * @version $Id$
 */
public class LLVMStoreInstruction extends LLVMInstruction {

    /**
     * @param state The state in which we consider <code>pointerRef</code>.
     * @param pointerRef Some pointer to store to.
     * @param type The pointer type of <code>pointerRef</code>.
     * @param allocationIndex The allocation index to which <code>pointerRef</code> is known to be associated to.
     * @return A set of references and target types for which we do not definitely know that they do not share with
     *         <code>pointerRef</code> and <code>targetType</code> in <code>state</code> and the specified state
     *         possibly updated during the association checks.
     */
    private static Pair<Set<LLVMMemoryRange>, LLVMAbstractState> getAccessesPossiblySharingWith(
        LLVMAbstractState state,
        LLVMSimpleTerm pointerRef,
        LLVMPointerType type,
        Integer allocationIndex,
        Abortion aborter
    ) {
        LLVMAbstractState newState = state;
        
        final Set<LLVMMemoryRange> possiblySharingAccesses = new LinkedHashSet<LLVMMemoryRange>();
        // Use knowledge about the stored data: If their (abstract) values are disjoint, then they cannot be equal.
        for (LLVMMemoryRange otherRefOnHeap : newState.getMemory().keySet()) {
        	Pair<Boolean,LLVMAbstractState> possiblySharing = possiblySharingWith(otherRefOnHeap, newState, pointerRef, type, allocationIndex,aborter);
        	newState = possiblySharing.y;
        	if(possiblySharing.x)
        		possiblySharingAccesses.add(otherRefOnHeap);
        }
        return new Pair<Set<LLVMMemoryRange>, LLVMAbstractState>(possiblySharingAccesses, newState);
    }
    
    /**
     * @param state The state in which we consider <code>pointerRef</code>.
     * @param pointerRef Some pointer to store to.
     * @param type The pointer type of <code>pointerRef</code>.
     * @param allocationIndex The allocation index to which <code>pointerRef</code> is known to be associated to.
     * @param otherRefOnHeap The heap range to check if it is possibly affected by storing to pointerRef
     * @return A pair (x,y) where x is true if this store instruction may change the range otherRefOnHeap
     * 			and y is the refined version of state
     */
    private static Pair<Boolean,LLVMAbstractState> possiblySharingWith(
    		LLVMMemoryRange otherRefOnHeap,
    		LLVMAbstractState state,
            LLVMSimpleTerm pointerRef,
            LLVMPointerType type,
            Integer allocationIndex,
            Abortion aborter) {
    	final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMConstant offset = termFactory.constant(type.toOffset());
    	
        // If the references belong to different allocations, they cannot share
        final LLVMPointerType otherPointerType =
            new LLVMPointerType(otherRefOnHeap.getType(), state.getModule().getPointerSize(), null);
        final Pair<LLVMAssociationIndex, LLVMAbstractState> otherIndex =
            state.getAssociatedAllocationIndex(otherRefOnHeap.getFromRef(), otherPointerType, false,aborter);
        state = otherIndex.y;
        if (allocationIndex == null || otherIndex.x == null || allocationIndex.equals(otherIndex.x.x)) {
            if (allocationIndex != null && otherIndex.x == null && otherRefOnHeap instanceof LLVMMemoryRecursiveRange) {
                // struct pointers without allocation have lost their (distinct) allocation while merging;
                // they do not share with other variables in present allocations
                // TODO correct?
                return new Pair<>(false,state);
            }
            Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(
                    relationFactory.lessThan(
                        termFactory.add(
                            otherRefOnHeap.getToRef(),
                            termFactory.constant(otherPointerType.toOffset())
                        ),
                        pointerRef
                    ),
                    aborter
                );
            state = check.y;
            if (!check.x) {
                check =
                    state.checkRelation(
                        relationFactory.lessThan(termFactory.add(pointerRef, offset), otherRefOnHeap.getFromRef()), aborter
                    );
                state = check.y;
                if (!check.x) {
                    return new Pair<>(true,state);
                }
            }
        }
        return new Pair<>(false,state);
    }
    
    /**
     * 
     * @param state
     * @param memoryRange
     * @return True if it is possible that this store modifies memory stored in <code>memoryRange</code> in <code>state</code>
     * Note: We do not check memory safety here: You must make sure that we know were this store goes to (i.e. the allocation) 
     */
    public boolean possiblySharingWith(LLVMAbstractState state, LLVMMemoryRange memoryRange, Abortion aborter) {
    	
    	LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.addressValue);
    	LLVMPointerType type = this.addressValue.getType().getThisAsPointerType();
    	Pair<LLVMAssociationIndex, LLVMAbstractState> allocationIndex =
                state.getAssociatedAllocationIndex(pointerRef, type, false, aborter);
    	
    	if(allocationIndex.x.x == null)
    		throw new IllegalStateException("Only use this method if storing to a known allocation");
    	
    	return possiblySharingWith(memoryRange, state, pointerRef, type, allocationIndex.x.x,aborter).x;
    }

    /**
     * The pointer.
     */
    private final LLVMLiteral addressValue;

    /**
     * Alignment information (optional - maybe null).
     */
    private final LLVMLiteral alignment;

    /**
     * The value to store.
     */
    private final LLVMLiteral valueToStore;

    /**
     * Creates a sequential instruction which is not the first one in a function.
     * @param val The value to store.
     * @param addr The address where to store the value.
     * @param align Alignment information.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMStoreInstruction(LLVMLiteral val, LLVMLiteral addr, LLVMLiteral align, int debugLine) {
        super(debugLine);
        this.addressValue = addr;
        this.alignment = align;
        this.valueToStore = val;
    }

    @Override
    public void addConeVariables(Set<String> coneVars) {
        LLVMInstruction.collectVariable(coneVars, this.addressValue);
        LLVMInstruction.collectVariable(coneVars, this.valueToStore);
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.addressValue);
        LLVMInstruction.collectVariable(vars, this.valueToStore);
    }
    
    public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        return null;
    }

    @Override
    public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    ) {
        final LLVMTermFactory termFactory = params.SMTsolver.stateFactory.getRelationFactory().getTermFactory();
        Set<Pair<IntegerRelationSet, List<String>>> res = new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
        if (!(this.addressValue instanceof LLVMVariableLiteral)) {
            // we cannot infer conditions - the set is empty
            return res;
        }
        LLVMSimpleTerm valRef;
        if (this.valueToStore instanceof LLVMVariableLiteral) {
            String valName = ((LLVMVariableLiteral)this.valueToStore).getName();
            valRef = new LLVMHeuristicProgVarRef(valName, valName);
        } else if (this.valueToStore instanceof LLVMBigIntLiteral) {
            valRef = termFactory.constant(((LLVMBigIntLiteral)this.valueToStore).getValueAsBigInteger());
        } else if (this.valueToStore instanceof LLVMRegularIntLiteral) {
            valRef = termFactory.constant(((LLVMRegularIntLiteral)this.valueToStore).getValueAsBigInteger());
        } else {
            // we cannot infer conditions - the set is empty
            return res;
        }
        String addrName = ((LLVMVariableLiteral)this.addressValue).getName();
        LLVMHeapVarRef addrVariable = new LLVMHeapVarRef(addrName, addrName);
        outer: for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            IntegerRelationSet relSet = new IntegerRelationSet();
            for (IntegerRelation rel : pair.x) {
                for (Variable ref : rel.getVariables()) {
                    if (!(ref instanceof LLVMHeapVarRef)) {
                        continue;
                    }
                    if (!ref.equals(addrVariable)) {
                        // we possibly lose necessary information about the heap - so drop this return condition
                        continue outer;
                    }
                }
                relSet.add(rel.applySubstitution(addrVariable, valRef));
            }
            res.add(new Pair<IntegerRelationSet, List<String>>(relSet, pair.y));
        }
        return res;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException, MemorySafetyException {
        // determine the value of the pointer
        LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.addressValue);
        LLVMSimpleTerm refToStore = state.getSimpleTermForLiteral(this.valueToStore);
        if (state.isPossiblyTrapValue(pointerRef) || state.isPossiblyTrapValue(refToStore)) {
            throw new TrapValueException(nodeNumber);
        }
        LLVMPointerType type = this.addressValue.getType().getThisAsPointerType();
        LLVMType targetType = type.getTargetType();
        Pair<LLVMAssociationIndex, LLVMAbstractState> allocationIndex =
            state.getAssociatedAllocationIndex(pointerRef, type, false, aborter);
        LLVMAbstractState res = allocationIndex.y;
        if (proveMemorySafety && allocationIndex.x == null) {
            throw new MemorySafetyException(nodeNumber);
        }
        // check alignment
        if (!state.getStrategyParamters().useOptimizations && this.alignment != null) {
            int align = this.alignment.toInt();
            if (Globals.useAssertions) {
                // clang requires this; llvm specification seems not to be specific about it.
                assert (IntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
            }
            if (align > 1) {
                final Pair<Boolean, ? extends LLVMAbstractState> check =
                    res.checkRelation(
                        res.getRelationFactory().createAlignmentRelation(
                            pointerRef,
                            res.getRelationFactory().getTermFactory().constant(BigInteger.valueOf(align))
                        ),
                        aborter
                    );
                res = check.y;
                if (proveMemorySafety && !check.x) {
//                    throw new UndefinedBehaviorException("Wrong alignment at node " + nodeNumber + ".");
                }
            }
        }
        /*
         * We now need to handle side-effects, i.e., remove information about values which might be influenced by
         * this write. However, as symbolic variables statically reference a fixed value, and a new value is
         * represented by a fresh variable, we can solve the problem by just removing dereferencing information for all
         * values for which we cannot guarantee that they are not influenced.
         * The only way a store can havoc values is by destroying heap connections for entries not sure to be
         * non-sharing with the reference where the store works. Other cases are covered by the abstraction of values
         * to references since a reference does not change its value - only the heap structure might change and this
         * is covered by the heap connections.
         */
        boolean unsigned;
        if (state.getStrategyParamters().useBoundedIntegers) {
            unsigned = state.getModule().getUnsignedBitvectorVariables().contains(this.valueToStore.getName());
        } else {
            unsigned = state.getModule().getUnsignedUnboundedVariables().contains(this.valueToStore.getName());;
        }
        Integer index = null;
        if (allocationIndex.x != null) {
            index = allocationIndex.x.x;
        }
        final Pair<Set<LLVMMemoryRange>, LLVMAbstractState> sharePair =
            LLVMStoreInstruction.getAccessesPossiblySharingWith(res, pointerRef, type, index, aborter);
        Set<Pair<LLVMMemoryRange, LLVMIntervalMemoryInvariant>> doNotRemove =
            new LinkedHashSet<Pair<LLVMMemoryRange, LLVMIntervalMemoryInvariant>>();
        if (res instanceof LLVMHeuristicState) {
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> heapEntry : res.getMemory().entrySet()) {
                LLVMMemoryRange range = heapEntry.getKey();
                if (sharePair.x.contains(range) && !(range.isPointwise()) && heapEntry.getValue() instanceof LLVMIntervalMemoryInvariant) {
                    LLVMIntervalMemoryInvariant inv = (LLVMIntervalMemoryInvariant) heapEntry.getValue();
                    LLVMValue value = ((LLVMHeuristicState)res).getValue((LLVMHeuristicVariable)refToStore);
                    if (
                        inv.subset(
                            value.getThisAsAbstractBoundedInt().getLower(),
                            value.getThisAsAbstractBoundedInt().getUpper()
                        )
                    ) {
                        doNotRemove.add(new Pair<LLVMMemoryRange, LLVMIntervalMemoryInvariant>(range, inv));
                    }
                }
            }
        }
        res = sharePair.y;
        //Tell the MemoryChangeTracker what we did:
        if(memoryTracker != null) {
        	LLVMAllocation alloc = state.getAllocations().get(allocationIndex.x.x);
        	memoryTracker.modifiedHeapWhenStoring(state, alloc, sharePair.x);
        }
        if(res.getAllocationChangedSinceEntryStateMap() != null) {
        	//This state carries boolean flags for which allocations were modified
        	Boolean entryForModifiedAllocation = res.getAllocationChangedSinceEntryStateMap().get(allocationIndex.x.x);
        	if(entryForModifiedAllocation != null && !entryForModifiedAllocation) {
        		Map<Integer,Boolean> mutableCopy = new LinkedHashMap<>(res.getAllocationChangedSinceEntryStateMap());
        		mutableCopy.put(allocationIndex.x.x, true);
        		res = res.setAllocationChangedSinceEntryState(ImmutableCreator.create(mutableCopy));
        	}
        	
        }
        
        
        res = res.removeHeapAccesses(sharePair.x);
        for (Pair<LLVMMemoryRange, LLVMIntervalMemoryInvariant> pair : doNotRemove) {
            res = res.setHeapEntry(pair.x, pair.y);
        }
        if (LLVMDebuggingFlags.SV_COMP_MODE && refToStore == null) {
            // parameters of function main; should never be loaded
            return Collections.singleton(new LLVMSymbolicEvaluationResult(res.incrementPC(), Collections.emptySet()));
        }
        res =
            res.setSimpleHeapEntry(
                pointerRef,
                targetType,
                unsigned,
                refToStore,
                aborter
            ).incrementPC();
        /*
         * Try to merge heap ranges into bigger ones. To do so we enumerated all adjacent heap ranges and then
         * we check if the underlying invariants are compatible.
         */
        res = res.findAndCreateInvariantsForAccess(new LLVMMemoryRange(pointerRef, pointerRef, targetType, unsigned),aborter);
        /*
         * Try to merge heap ranges into bigger struct invariants, if any present.
         */
        LLVMSymbolicEvaluationResult evalRes = res.findAndCreateStructInvariants(new LLVMMemoryRange(pointerRef, pointerRef, targetType, unsigned),aborter);
        //TODO merge the newly created bigger invariants as well
        
        return Collections.singleton(evalRes);
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        boolean unsigned;
        if (state.getStrategyParamters().useBoundedIntegers) {
            unsigned = state.getModule().getUnsignedBitvectorVariables().contains(this.valueToStore.getName());
        } else {
            unsigned = state.getModule().getUnsignedUnboundedVariables().contains(this.valueToStore.getName());;
        }
        final LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.addressValue);
        final LLVMPointerType type = this.addressValue.getType().getThisAsPointerType();
        Pair<LLVMAssociationIndex, LLVMAbstractState> allocationIndex =
                state.getAssociatedAllocationIndex(pointerRef, type, false, aborter);
        final Pair<Set<LLVMMemoryRange>, LLVMAbstractState> sharePair =
                LLVMStoreInstruction.getAccessesPossiblySharingWith(state, pointerRef, type, allocationIndex.x.x, aborter);

        for (LLVMMemoryRange affectedMemoryRange : sharePair.x) {
            if (!affectedMemoryRange.equals(new LLVMMemoryRange(pointerRef, pointerRef, type.getTargetType(), unsigned))) {
                // Other memory area is affected by this store instruction. This may lead to over-approximation
                return true;
            }
        }
        return false;
    }
    
    
    
    /**
     * 
     * @return The allocation of <code>state</code> which this store modifies, or null if we don't know it (violation of memory safety)
     */
    /* "Deactivated" by Frank because currently not in use and there are already plenty of methods in here dealing with potential sharing
     * public LLVMAllocation getAllocationStoringTo(LLVMAbstractState state, Abortion aborter) {
    	LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.addressValue);
    	LLVMPointerType type = this.addressValue.getType().getThisAsPointerType();
    	Pair<LLVMAssociationIndex, LLVMAbstractState> allocationIndex =
                state.getAssociatedAllocationIndex(pointerRef, type, false,aborter);
    	
    	if(allocationIndex == null || allocationIndex.x == null )
    		return null;
    	
    	return state.getAllocations().get(allocationIndex.x.x);
    }*/
    
    //@Deprecated
    /* "Deactivated" by Frank because currently not in use and there are already plenty of methods in here dealing with potential sharing
     * public boolean possiblyStoresTo(LLVMAbstractState state, LLVMAllocation allocation, Abortion aborter) {
    	if(allocation.x == null || allocation.y == null)
    		throw new IllegalArgumentException("Illegal allocation");
    	
    	LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.addressValue);
    	LLVMPointerType type = this.addressValue.getType().getThisAsPointerType();
    	Pair<LLVMAssociationIndex, LLVMAbstractState> allocationIndex =
        state.getAssociatedAllocationIndex(pointerRef, type, false, aborter);
    	
    	if(allocationIndex.x == null) {
    		//This can only happen if we did not want to prove memory safety.
    		return true;
    	}
    	
    	LLVMAllocation actualAllocation = state.getAllocations().get(allocationIndex.x.x);
    	
    	if(actualAllocation == null)
    		throw new IllegalStateException("Excepted proper allocation");
    	
    
    	
    	if(allocation.x.equals(actualAllocation.x) && allocation.y.equals(actualAllocation.y))
    		return true;
    	
    	
    	
    	LLVMRelation lowerBordersDontMatch = state.getRelationFactory().createRelation(IntegerRelationType.NE, allocation.x, actualAllocation.x);
    	LLVMRelation upperBordersDontMatch = state.getRelationFactory().createRelation(IntegerRelationType.NE, allocation.y, actualAllocation.y);
    	
    	Boolean lowerBorderResult = state.checkRelation(lowerBordersDontMatch, aborter).x;
    	Boolean upperBorderResult = state.checkRelation(upperBordersDontMatch, aborter).x;
    	
    	if(lowerBorderResult && upperBorderResult)
    		return true;
    	
    	for(LLVMAllocation allocationOfState : state.getAllocations()) {
    		if(allocationOfState.equals(actualAllocation))
    			continue;
    		if(allocationOfState.equals(allocation))
    			return false;
    	}
    	
    	
    	
    	return true;
    }*/

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext("store "));
        res.append(eu.tttext(this.valueToStore.toString()));
        res.append(eu.tttext(", "));
        res.append(eu.tttext(this.addressValue.toString()));
        return res.toString();
    }

    /**
     * @return The pointer.
     */
    public LLVMLiteral getAddressValue() {
        return this.addressValue;
    }

    /**
     * @return The alignment information.
     */
    public LLVMLiteral getAlignment() {
        return this.alignment;
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // the address is interesting because it causes refinement
        LLVMInstruction.collectVariable(vars, this.addressValue);
        return vars;
    }

    @Override
    public String getProducedVariable() {
        return null;
    }

    /**
     * @return The value to store.
     */
    public LLVMLiteral getStoredValue() {
        return this.valueToStore;
    }

    @Override
    public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
        LLVMProgramPosition newPos = new LLVMProgramPosition(pos.x, pos.y, pos.z + 1);
        if (Globals.useAssertions) {
            assert module.getInstruction(newPos) != null;
        }
        return Collections.singletonList(newPos);
    }

    // TODO check whether a refinement like this is useful at all
//    @Override
//    public Set<LLVMSymbolicEvaluationResult> refine(LLVMAbstractState state, int nodeNumber) {
//        // determine the value of the pointer
//        //LLVMReference pointerRef = state.getRefForLiteral(this.addressValue);
//        BasicType type = this.addressValue.getType();
//        // ensure to set all pointer sizes correctly (should probably be done while parsing)
//        type = type.setSizes(module.getPointerSize());
//        //BasicType targetType = ((BasicPointerType)type).getTargetType(); MERGED?? Not sure about this
//        // if an initial heap address may be overwritten by a store to a possibly different address, we do a case
//        // analysis over whether these addresses are equal or not
//        LLVMHeuristicVariable TargetRef = state.getTermForLiteral(this.addressValue);
//        BasicType targetType = ((BasicPointerType)type).getTargetType();
//        Set<HeapRange> notSharingWithTarget =
//            StoreInstruction.getAccessesNotSharingWith(state, TargetRef, targetType, params);
//        Collection<LLVMHeuristicVariable> initialHeapAddrs = state.getInitialHeapAddresses().values();
//        for (HeapRange access : state.getHeap().keySet()) {
//            if (!initialHeapAddrs.contains(access.getFromRef()) || notSharingWithTarget.contains(access)) {
//                continue;
//            }
//            assert(access.isPointwise());
//            // we would lose knowledge about an initial heap address - check for equality
//            if (
//                IntegerUtils.truthValueOfRelation(
//                    state,
//                    TargetRef,
//                    IntegerRelationType.EQ,
//                    access.getFromRef(),
//                    true,
//                    params
//                ) == YNM.MAYBE
//            ) {
//                return IntegerUtils.addRelationAndInverse(
//                    state,
//                    TargetRef,
//                    IntegerRelationType.EQ,
//                    access.getFromRef(),
//                    params
//                );
//            }
//        }
//        // Otherwise a store either works on allocated memory (all is good) or not (not memory safe => we must give up)
//        // - there is nothing else to refine.
//        return null;
//    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("StoreInstr ");
        strBuilder.append(" storedType: " + this.valueToStore.getType());
        strBuilder.append(" storedValue: " + this.valueToStore);
        strBuilder.append(" addrType: " + this.addressValue.getType());
        strBuilder.append(" addrValue: " + this.addressValue);
        if (this.alignment != null) {
            strBuilder.append(" alignment: " + this.alignment);
        }
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append("store ");
        res.append(this.valueToStore.toDOTString());
        res.append(", ");
        res.append(this.addressValue);
        return res.toString();
    }

    @Override
    public String toString() {
        return "store " + this.valueToStore + ", " + this.addressValue;
    }

}
