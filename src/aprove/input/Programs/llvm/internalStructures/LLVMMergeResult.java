package aprove.input.Programs.llvm.internalStructures;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convenience class to build and hold results of an abstract state generalization.
 * @author Marc Brockschmidt, cryingshadow
 */
public class LLVMMergeResult {

    /**
     * The reference result to achieve an instance check.
     */
    public static final LLVMMergeResult INSTANCE_REFERENCE_RESULT = new LLVMMergeResult(Double.POSITIVE_INFINITY, 0);

    /**
     * The reference result to achieve a merging of two states.
     */
    public static final LLVMMergeResult MERGING_REFERENCE_RESULT =
        new LLVMMergeResult(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);

    /**
     * A mapping from indices in the generalized state to triples of indices (for allocated memory areas) in the
     * newer/older state and an enum indicating whether the area has been allocated within the current function frame
     * or by malloc or not. The left element of the pairs always belongs to the newer state.
     */
    private final Map<Integer, AllocationMapping> areaMapping;

    /**
     * The result of generalizing <code>newerState</code> with
     * <code>olderState</code> (starts out as copy of newerState).
     */
    private LLVMAbstractState generalizedState;

    /**
     * Cache for refs from the newer state which have already been merged.
     */
    private final Set<LLVMSimpleTerm> mergedNewerRefs;

    /**
     * Cache for refs from the older state which have already been merged.
     */
    private final Set<LLVMSimpleTerm> mergedOlderRefs;

    /**
     * The newly created state that triggered the generalization.
     */
    private final LLVMAbstractState newerState;

    /**
     * The cost of this generalization step from the newer state, i.e., an
     * arbitrary measure of how coarse the abstraction is.
     */
    private double newToGeneralizedCost;

    /**
     * The number of allocated areas in the merged state.
     */
    private int numOfMergedAllocs;

    /**
     * Some older state that is used as basis for generalization.
     */
    private final LLVMAbstractState olderState;

    /**
     * The cost of this generalization step from the older state, i.e., an
     * arbitrary measure of how coarse the abstraction is.
     */
    private double oldToGeneralizedCost;

    /**
     * This is the currently known best result (or null, if none is known)
     * for the generalization of the same state.
     *
     * In the generalization process, we stop as soon as our result becomes
     * worse than the reference result, which is when either the total
     * difference of the new generalization exceeds the total difference of
     * the reference result, or when this holds for the difference between
     * the older and result states.
     */
    private final LLVMMergeResult referenceResult;

    /**
     * A mapping from pairs of references in the newer/older state to
     * references in the generalized state. The left element of the pairs
     * always belongs to the newer state.
     *
     * Note that references might appear several times on the left and on the
     * right. As example, consider three variables %a, %b, %c and two states
     * with
     *  newerState:   %a: v1, %b: v1, %c: v2
     *  olderState:   %a: v3, %b: v4, %c: v4
     * Then, our map would contain
     *  (v1,v3) -> v5
     *  (v1,v4) -> v6
     *  (v2,v4) -> v7
     * and our generalized state would look like this:
     *  generalizedState:   %a: v5, %b: v6, %c: v7
     */
    private final Map<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> refMapping;

    /**
     * The factory to build terms.
     */
    private final LLVMTermFactory termFactory;

    /**
     * @param refResult the currently known best result (or null, if none is known)
     * @param oldS older state that is used as basis for generalization
     * @param newS newly created state that triggered the generalization
     * @param factory The factory to build terms.
     */
    public LLVMMergeResult(
        LLVMMergeResult refResult,
        LLVMAbstractState oldS,
        LLVMAbstractState newS,
        LLVMTermFactory factory
    ) {
        this.referenceResult = refResult;
        this.olderState = oldS;
        this.newerState = newS;
        this.generalizedState = newS;
        this.refMapping = new LinkedHashMap<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm>();
        this.mergedNewerRefs = new LinkedHashSet<LLVMSimpleTerm>();
        this.mergedOlderRefs = new LinkedHashSet<LLVMSimpleTerm>();
        this.areaMapping = new LinkedHashMap<Integer, AllocationMapping>();
        this.numOfMergedAllocs = 0;
        this.newToGeneralizedCost = 0;
        this.oldToGeneralizedCost = 0;
        this.termFactory = factory;
    }

    /**
     * Only for private use to create one-off reference results.
     * @param newToGenCost maximal costs from the new state to the generalized one
     * @param oldToGenCost maximal costs from the old state to the generalized one
     */
    private LLVMMergeResult(double newToGenCost, double oldToGenCost) {
        this.referenceResult = null;
        this.olderState = null;
        this.newerState = null;
        this.generalizedState = null;
        this.refMapping = null;
        this.mergedNewerRefs = null;
        this.mergedOlderRefs = null;
        this.areaMapping = null;
        this.numOfMergedAllocs = 0;
        this.newToGeneralizedCost = newToGenCost;
        this.oldToGeneralizedCost = oldToGenCost;
        this.termFactory = null;
    }

    /**
     * Note some cost in this generalization.
     *
     * @param newCost the type of the cost
     * @param fromNewer true if this cost describes a difference between
     *  newer state and the result, false if it describes a difference between
     *  the older state and the result.
     * @throws TooExpensiveException if the costs exceed the costs of the
     *  reference result
     */
    public void addCost(LLVMCost newCost, boolean fromNewer) throws TooExpensiveException {
        if (fromNewer) {
            this.newToGeneralizedCost += newCost.getCostValue();
        } else {
            this.oldToGeneralizedCost += newCost.getCostValue();
            if (this.oldToGeneralizedCost > this.referenceResult.oldToGeneralizedCost) {
                throw new TooExpensiveException("Diff between old state and result too big after adding " + newCost);
            }
        }
        if (this.getTotalCost() > this.referenceResult.getTotalCost()) {
            throw new TooExpensiveException("Diff between old state and result too big after adding " + newCost);
        }
    }

    /**
     * @return A mapping from allocated areas in the newer state to the ones in the older state.
     */
    public Map<Integer, Integer> getAllocationBijection() {
        Map<Integer, Integer> res = new LinkedHashMap<Integer, Integer>();
        for (Map.Entry<Integer, AllocationMapping> entry : this.areaMapping.entrySet()) {
            AllocationMapping triple = entry.getValue();
            res.put(triple.x, triple.y);
        }
        return res;
    }

    /**
     * @param fromOlder Flag indicating whether to map the areas in the older (true) or newer (false) state to the ones
     *                  in the merged state.
     * @return A mapping from allocated areas in the older or newer state to the ones in the merged state.
     */
    public Map<Integer, Integer> getAllocationBijection(boolean fromOlder) {
        Map<Integer, Integer> res = new LinkedHashMap<Integer, Integer>();
        for (Map.Entry<Integer, AllocationMapping> entry : this.areaMapping.entrySet()) {
            res.put(fromOlder ? entry.getValue().y : entry.getValue().x, entry.getKey());
        }
        return res;
    }

    /**
     * @param index The index to look a partner for.
     * @param fromOlderState Flag indicating whether the index belongs to the older state.
     * @return The index of the other state with which the specified one has been merged or -1 if no such index exists.
     */
    public int getAllocationPartner(int index, boolean fromOlderState) {
        if (fromOlderState) {
            for (AllocationMapping triple : this.areaMapping.values()) {
                if (index == triple.y) {
                    return triple.x;
                }
            }
        } else {
            for (AllocationMapping triple : this.areaMapping.values()) {
                if (index == triple.x) {
                    return triple.y;
                }
            }
        }
        return -1;
    }

    /**
     * @return the generalization result.
     */
    public LLVMAbstractState getGeneralizedState() {
        return this.generalizedState;
    }

    /**
     * @param index An index from the merge-state.
     * @param instIsNewerState Flag indicating whether the inst-state is the newer state.
     * @return A triple of corresponding indices from the inst- and of-state and an enum indicating whether the
     *         corresponding areas have been allocated within the current function's frame or by malloc or not.
     */
    public AllocationMapping getAllocationMappingForMergedIndex(int index, boolean instIsNewerState) {
        AllocationMapping res = this.areaMapping.get(index);
        if (instIsNewerState) {
            return res;
        } else {
            return new AllocationMapping(res.y, res.x, res.z);
        }
    }

    /**
     * @param instIsNewerState indicates if the instance state is the newer or older state.
     * @return the newer or older state, depending on the input.
     */
    public LLVMAbstractState getInstState(boolean instIsNewerState) {
        if (instIsNewerState) {
            return this.newerState;
        } else {
            return this.olderState;
        }
    }

    /**
     * @param instIndex The index from the inst-state.
     * @param ofIndex The index from the of-state.
     * @param instIsNewerState Flag indicating whether the inst-state is the newer state.
     * @return The index from the merge-state or -1 if the specified indices have not been merged together.
     */
    public int getMergedArea(int instIndex, int ofIndex, boolean instIsNewerState) {
        int newIndex = instIsNewerState ? instIndex : ofIndex;
        int oldIndex = instIsNewerState ? ofIndex : instIndex;
        for (Map.Entry<Integer, AllocationMapping> entry : this.areaMapping.entrySet()) {
            AllocationMapping triple = entry.getValue();
            if (triple.x.equals(newIndex) && triple.y.equals(oldIndex)) {
                return entry.getKey();
            }
        }
        return -1;
    }

    /**
     * @param instIsNewerState Flag indicating whether the inst-state is the newer state.
     * @return The set of already merged references in the of-state.
     */
    public Set<LLVMSimpleTerm> getMergedOfRefs(boolean instIsNewerState) {
        Set<LLVMSimpleTerm> res = new LinkedHashSet<LLVMSimpleTerm>();
        if (instIsNewerState) {
            for (Pair<LLVMSimpleTerm, LLVMSimpleTerm> pair : this.refMapping.keySet()) {
                res.add(pair.y);
            }
        } else {
            for (Pair<LLVMSimpleTerm, LLVMSimpleTerm> pair : this.refMapping.keySet()) {
                res.add(pair.x);
            }
        }
        return res;
    }

    /**
     * @param instRef one reference
     * @param ofRef another reference
     * @param instIsNewerState indicates if the <code>instRef</code> belongs to the newer
     *  state or not. <code>ofRef</code> is automatically in the other.
     * @return the name of the known merge result of the two references.
     */
    public LLVMSimpleTerm getMergedRef(
        LLVMSimpleTerm instRef,
        LLVMSimpleTerm ofRef,
        boolean instIsNewerState
    ) {
        if (!instIsNewerState) {
            return this.getMergedRef(ofRef, instRef, true);
        }
        if (instRef instanceof LLVMNonMergedConstRef) {
            return ((LLVMNonMergedConstRef)instRef).asNormal();
        }
        return this.refMapping.get(new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(instRef, ofRef));
    }

    /**
     * @return newly created state that triggered the generalization.
     */
    public LLVMAbstractState getNewerState() {
        return this.newerState;
    }

    /**
     * @return The number of allocated areas in the merged state.
     */
    public int getNumberOfMergedAreas() {
        return this.numOfMergedAllocs;
    }

    /**
     * @param instIsNewerState indicates if the instance state is the newer or older state.
     * @return the older or newer state, depending on the input.
     */
    public LLVMAbstractState getOfState(boolean instIsNewerState) {
        if (instIsNewerState) {
            return this.olderState;
        } else {
            return this.newerState;
        }
    }

    /**
     * @return older state that is used as basis for generalization.
     */
    public LLVMAbstractState getOlderState() {
        return this.olderState;
    }

    /**
     * @return The reference result for cost calculations.
     */
    public LLVMMergeResult getReferenceResult() {
        return this.referenceResult;
    }

    /**
     * @return Mapping from pairs of references in the newer/older state to references in the generalized state.
     *         Changes to this mapping are backed by the generalization result and vice versa.
     */
    public Map<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> getRefMapping() {
        return this.refMapping;
    }

    /**
     * @param ref Some reference.
     * @param isFromOlderState Flag indicating whether the reference is from the older state.
     * @return A set of references in the other state which occurred at some position (variable, dereferencing of
     *         variable) at the same place as <code>ref</code>.
     */
    public Set<LLVMSimpleTerm> getRefPartners(LLVMSimpleTerm ref, boolean isFromOlderState) {
        Set<LLVMSimpleTerm> res = new LinkedHashSet<LLVMSimpleTerm>();
        for (Pair<LLVMSimpleTerm, LLVMSimpleTerm> p : this.refMapping.keySet()) {
            if (isFromOlderState) {
                if (p.y.equals(ref)) {
                    res.add(p.x);
                }
            } else {
                if (p.x.equals(ref)) {
                    res.add(p.y);
                }
            }
        }
        return res;
    }

    /**
     * @return the total cost of this generalization
     */
    public double getTotalCost() {
        return this.newToGeneralizedCost + this.oldToGeneralizedCost;
    }

    /**
     * @return true if the newer state is an instance of the older state.
     */
    public boolean isInstance() {
        return this.oldToGeneralizedCost == 0;
    }

    /**
     * Merges the indices of allocated areas. If both indices have already been merged, then nothing happens (the
     * return value then depends on the equality of the merged indices). If both indices have never been merged before,
     * a new index is created and both indices are mapped to the new index. If exactly one index has already been
     * merged before, nothing happens and false is returned.
     * @param instIndex The index in the inst-state.
     * @param ofIndex The index in the of-state.
     * @param stackFrameIndex The index of the stack frame where the allocation has been made in both states (negative
     *                        indices mean that the allocation has been done outside of the stack).
     * @param instIsNewerState Flag indicating whether the inst-state is the newer state.
     * @return True if the merge was successful. False if the merge could not be performed.
     */
    public boolean mergeAreas(int instIndex, int ofIndex, int stackFrameIndex, boolean instIsNewerState) {
        if (!instIsNewerState) {
            return this.mergeAreas(ofIndex, instIndex, stackFrameIndex, true);
        }
        if (Globals.useAssertions) {
            assert (instIndex >= 0 && ofIndex >= 0) : "Found negative index!";
        }
        int existingInst = -1;
        int existingOf = -1;
        boolean instUndef = true;
        boolean ofUndef = true;
        for (Map.Entry<Integer, AllocationMapping> entry : this.areaMapping.entrySet()) {
            AllocationMapping value = entry.getValue();
            if (instIndex == value.x) {
                existingInst = entry.getKey();
                instUndef = false;
                if (!ofUndef) {
                    break;
                }
            }
            if (ofIndex == value.y) {
                existingOf = entry.getKey();
                ofUndef = false;
                if (!instUndef) {
                    break;
                }
            }
        }
        if (instUndef && ofUndef) {
            // both are not yet mapped => create a new index
            this.areaMapping.put(this.numOfMergedAllocs++, new AllocationMapping(instIndex, ofIndex, stackFrameIndex));
            return true;
        } else {
            return existingInst == existingOf;
        }
    }

    /**
     * @param instRef One reference.
     * @param ofRef Another reference.
     * @param instIsNewerState Indicates whether the <code>instRef</code> belongs to the newer state or not.
     *                         <code>ofRef</code> is automatically in the other.
     * @param mergedValue The merged value for both references.
     * @return A fresh reference to represent the merge of <code>instRef</code> and <code>ofRef</code>, which is also
     *         noted in the internal map at the same time.
     * @throws TooExpensiveException If this got too expensive.
     */
    public LLVMSymbolicVariable mergeRefs(
        LLVMSimpleTerm instRef,
        LLVMSimpleTerm ofRef,
        boolean instIsNewerState
    ) throws TooExpensiveException {
        if (!instIsNewerState) {
            return this.mergeRefs(ofRef, instRef, true);
        }
        StringBuilder debugName = new StringBuilder();
        debugName.append(instRef.getName());
        debugName.append("/");
        debugName.append(ofRef.getName());
        LLVMSymbolicVariable newRef = this.termFactory.freshVariable(debugName.toString());
        if (this.mergedNewerRefs.contains(instRef)) {
            this.addCost(LLVMCost.MULTIPLE_REFERENCE_MERGE, true);
        } else {
            this.mergedNewerRefs.add(instRef);
        }
        if (this.mergedOlderRefs.contains(ofRef)) {
            this.addCost(LLVMCost.MULTIPLE_REFERENCE_MERGE, false);
        } else {
            this.mergedOlderRefs.add(ofRef);
        }
        this.refMapping.put(new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(instRef, ofRef), newRef);
        return newRef;
    }
    
    public void removeMergeAreaEntry(int index) {
        int i = index;
        for (i = index; i < this.numOfMergedAllocs-1; i++) {
            this.areaMapping.put(i, this.areaMapping.get(i+1));
        }
        this.areaMapping.remove(i);
        this.numOfMergedAllocs--;
    }

    /**
     * @param instRef One reference.
     * @param ofRef Another reference.
     * @param instIsNewerState Indicates if the <code>instRef</code> belongs to the newer state or not.
     *                         <code>ofRef</code> is automatically in the other.
     * @return True iff we already know about a merge result for these two references.
     */
    public boolean refPairAlreadyMerged(
        LLVMSymbolicVariable instRef,
        LLVMSymbolicVariable ofRef,
        boolean instIsNewerState
    ) {
        if (!instIsNewerState) {
            return this.refPairAlreadyMerged(ofRef, instRef, true);
        }
        return this.refMapping.containsKey(new Pair<LLVMSymbolicVariable, LLVMSymbolicVariable>(instRef, ofRef));
    }

    /**
     * @param genS The new generalized state.
     */
    public void setGeneralizedState(LLVMAbstractState genS) {
        this.generalizedState = genS;
    }

    /**
     * Stack frame index marking an allocation by malloc.
     */
    public static final int ALLOCATION_BY_MALLOC = -1;

    /**
     * Give a name to triples of integers storing an allocation mapping.
     * @author cryingshadow
     * @version $Id$
     */
    public static class AllocationMapping extends Triple<Integer, Integer, Integer> {

        /**
         * @param newer The allocation index in the newer state.
         * @param older The allocation index in the older state.
         * @param stackFrame The index of the stack frame where the allocation has been made in both states (negative
         *                   indices mean that the allocation has been done outside of the stack).
         */
        public AllocationMapping(Integer newer, Integer older, Integer stackFrame) {
            super(newer, older, stackFrame);
        }

    }

}
