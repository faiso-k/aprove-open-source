package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * An invariant (first,last,additiveChange) to represent values of a recursive data structure,
 * where the nth value is first + n*additiveChange.
 * @author Jera Hensel
 */
public class LLVMComplexMemoryInvariant implements LLVMMemoryInvariant {
    
    private final LLVMSimpleTerm firstValue;
    
    private final LLVMSimpleTerm lastValue;
    
    private final LLVMAdditiveChange additiveChange;

    // The type of the values stored.
    private final LLVMType type;
    
    private final int hashCode = 17;
    
    /**
     * @param first
     * @param last
     * @param change
     * @param type
     */
    public LLVMComplexMemoryInvariant(LLVMSimpleTerm first, LLVMSimpleTerm last, LLVMAdditiveChange change, LLVMType type) {
        assert (change != null);
        this.firstValue = first;
        this.lastValue = last;
        this.additiveChange = change;
        this.type = type;
    }
    
    /**
     * @param list1
     * @param list2
     * @param type
     * @param mergedLengthRef
     * @param change The linear change of the values; null if not known.
     * @return A term that has to be added to the resulting state (null if there is none),
     *         and the deduced memory invariant.
     */
    public static LLVMComplexMemoryInvariant deduce(
        Set<LLVMHeuristicRelation> ofRels,
        Set<LLVMHeuristicRelation> instRels,
        List<LLVMSymbolicVariable> ofList,
        List<LLVMSymbolicVariable> instList,
        LLVMType type,
        Map<LLVMHeuristicVariable,Pair<BigInteger,BigInteger>> varOfInst,
        LLVMMergeResult mergeResult,
        boolean instIsNewerState
    ) {
        List<BigInteger> ofInts = new LinkedList<BigInteger>();
        List<BigInteger> instInts = new LinkedList<BigInteger>();
        boolean concrete = true;
        for (LLVMSymbolicVariable v : ofList) {
            if (v instanceof LLVMConstant) {
                ofInts.add(((LLVMConstant) v).getIntegerValue());
            } else {
                concrete = false;
            }
        }
        for (LLVMSymbolicVariable v : instList) {
            if (v instanceof LLVMConstant) {
                instInts.add(((LLVMConstant) v).getIntegerValue());
            } else {
                concrete = false;
            }
        }
        if (concrete) {
            return deduceConcrete(ofInts, instInts, type, varOfInst, mergeResult, instIsNewerState);
        }
        // We only deduce an invariant if
        // a) the length of one of the value sets (say x) is exactly one smaller than the length of the other set (say y)
        List<LLVMSymbolicVariable> smaller;
        List<LLVMSymbolicVariable> bigger;
        boolean ofIsSmaller;
        if (ofList.size() + 1 == instList.size()) {
            smaller = ofList;
            bigger = instList;
            ofIsSmaller = true;
        } else if (ofList.size() == instList.size() + 1) {
            smaller = instList;
            bigger = ofList;
            ofIsSmaller = false;
        } else if (ofList.size() == instList.size()) {
            // do not deduce something (but leave info as it is)
            return null;
        } else {
            return new LLVMComplexMemoryInvariant(null, null, null, type);
        }
        // determine change from relations
        BigInteger change = null;
        LLVMSortedType sortedType;
        if (ofIsSmaller && instList.size() == 2) {
            // check if instList[1] - instList[0] = change in instRels
            LLVMSymbolicVariable first = instList.get(0);
            LLVMSymbolicVariable second = instList.get(1);
            if (!(first instanceof LLVMConstant) && !(second instanceof LLVMConstant)) {
                for (LLVMHeuristicRelation rel : instRels) {
                    if (rel.getVariables().contains(first) && rel.getVariables().contains(second)) {
                        Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> triple =
                            rel.toOffByConstantPattern();
                        if (triple != null) {
                            if (triple.x.equals(first)) {
                                change = triple.z;
                            } else {
                                change = triple.z.negate();
                            }
                        }
                    }
                }
            }
        } else if (!ofIsSmaller && ofList.size() == 2) {
            // check if ofList[1] - ofList[0] = change in ofRels
            LLVMSymbolicVariable first = ofList.get(0);
            LLVMSymbolicVariable second = ofList.get(1);
            if (!(first instanceof LLVMConstant) && !(second instanceof LLVMConstant)) {
                for (LLVMHeuristicRelation rel : ofRels) {
                    if (rel.getVariables().contains(first) && rel.getVariables().contains(second)) {
                        Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> triple =
                            rel.toOffByConstantPattern();
                        if (triple != null) {
                            if (triple.x.equals(first)) {
                                change = triple.z;
                            } else {
                                change = triple.z.negate();
                            }
                        }
                    }
                }
            }
        }
        // and b) the first |x| values of y are equal to x, or the last |x| values of y are equal to x.
        if (!bigger.subList(0,bigger.size()-1).equals(smaller) && !bigger.subList(1,bigger.size()).equals(smaller)) {
            sortedType = LLVMSortedType.get(change);
            return new LLVMComplexMemoryInvariant(null, null, new LLVMAdditiveChange(change,sortedType), type);
        }
        // create a first and a last value if the references can be merged
        LLVMSimpleTerm first;
        if (ofIsSmaller) {
            first = mergeResult.getMergedRef(bigger.get(0), smaller.get(0), instIsNewerState);
        } else {
            first = mergeResult.getMergedRef(smaller.get(0), bigger.get(0), instIsNewerState);
        }
        LLVMSimpleTerm last;
        if (bigger.get(bigger.size()-1) instanceof LLVMConstant && bigger.get(bigger.size()-1).equals(smaller.get(smaller.size()-1))) {
            last = bigger.get(bigger.size()-1);
        } else {
            last = mergeResult.getMergedRef(smaller.get(smaller.size()-1), bigger.get(bigger.size()-1), instIsNewerState);
        }
        if (first != null) {
            if (last == null) {
                try {
                    if (ofIsSmaller) {
                        last = mergeResult.mergeRefs(bigger.get(bigger.size()-1), smaller.get(smaller.size()-1), instIsNewerState);
                    } else {
                        last = mergeResult.mergeRefs(smaller.get(smaller.size()-1), bigger.get(bigger.size()-1), instIsNewerState);
                    }
                    boolean unsigned = type.isPointerType();
                    LLVMValue lastValue = type.getInitializedIntValue(unsigned, mergeResult.getGeneralizedState().getStrategyParamters().useBoundedIntegers);
                    mergeResult.setGeneralizedState(((LLVMHeuristicState)mergeResult.getGeneralizedState()).setValue((LLVMHeuristicVariable)last, lastValue));
                } catch (TooExpensiveException e) {
                    // do nothing (so last is null)
                }
            }
        }
        sortedType = LLVMSortedType.get(change);
        return new LLVMComplexMemoryInvariant(first, last, new LLVMAdditiveChange(change,sortedType), type);
    }
    
    private static LLVMComplexMemoryInvariant deduceConcrete(
        List<BigInteger> ofList,
        List<BigInteger> instList,
        LLVMType type,
        Map<LLVMHeuristicVariable,Pair<BigInteger,BigInteger>> varOfInst,
        LLVMMergeResult mergeResult,
        boolean instIsNewerState
    ) {
        // We only deduce an invariant if
        // a) the length of one of the value sets (say x) is exactly one smaller than the length of the other set (say y)
        List<BigInteger> smaller;
        List<BigInteger> bigger;
        LLVMSortedType sortedType = LLVMSortedType.min(LLVMSortedType.get(ofList), LLVMSortedType.get(instList));
        boolean ofIsSmaller;
        if (ofList.size() + 1 == instList.size()) {
            smaller = ofList;
            bigger = instList;
            ofIsSmaller = true;
        } else if (ofList.size() == instList.size() + 1) {
            smaller = instList;
            bigger = ofList;
            ofIsSmaller = false;
        } else {
            return new LLVMComplexMemoryInvariant(null, null, new LLVMAdditiveChange(null,sortedType), type);
        }
        // and b) the first |x| values of y are equal to x, or the last |x| values of y are equal to x.
        if (!bigger.subList(0,bigger.size()-1).equals(smaller) && !bigger.subList(1,bigger.size()).equals(smaller)) {
            return new LLVMComplexMemoryInvariant(null, null, new LLVMAdditiveChange(null,sortedType), type);
        }
        // Then, try to find a pattern.
        BigInteger first = bigger.get(0);
        BigInteger second = bigger.get(1);
        BigInteger change = second.subtract(first);
        BigInteger last = null;
        for (BigInteger cur : bigger) {
            if (last != null) {
                if (!last.add(change).equals(cur)) {
                    // Too complex for us.
                    return new LLVMComplexMemoryInvariant(null, null, new LLVMAdditiveChange(null,sortedType), type);
                }
            }
            last = cur;
        }
        LLVMTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        // Now find the value that extends smaller to bigger and make this a variable depending on the length.
        if (bigger.subList(0,bigger.size()-1).equals(smaller)) {
            // smaller = [a]
            // bigger  = [a,b]
            // => if varOfInst values are a and b, we have found an invariant Inv(a..var;+change).
            for (Map.Entry<LLVMHeuristicVariable,Pair<BigInteger,BigInteger>> var : varOfInst.entrySet()) {
                BigInteger varOf = var.getValue().x;
                BigInteger varInst = var.getValue().y;
                BigInteger lastValueOf;
                BigInteger lastValueInst;
                if (ofIsSmaller) {
                    lastValueOf = smaller.get(smaller.size()-1);
                    lastValueInst = bigger.get(bigger.size()-1);
                } else {
                    lastValueInst = smaller.get(smaller.size()-1);
                    lastValueOf = bigger.get(bigger.size()-1);
                }
                if (varOf.equals(lastValueOf) && varInst.equals(lastValueInst)) {
                    return new LLVMComplexMemoryInvariant(termFactory.constant(first), var.getKey(), new LLVMAdditiveChange(change,sortedType), type);
                } else {
                    LLVMSimpleTerm smallerLastVar = termFactory.constant(smaller.get(smaller.size()-1));
                    LLVMSimpleTerm biggerLastVar = termFactory.constant(bigger.get(bigger.size()-1));
                    LLVMSymbolicVariable lastVar = null;
                    try {
                        if (ofIsSmaller) {
                            lastVar = mergeResult.mergeRefs(biggerLastVar, smallerLastVar, instIsNewerState);
                        } else {
                            lastVar = mergeResult.mergeRefs(smallerLastVar, biggerLastVar, instIsNewerState);
                        }
                        boolean unsigned = type.isPointerType();
                        LLVMValue lastValue = type.getInitializedIntValue(unsigned, mergeResult.getGeneralizedState().getStrategyParamters().useBoundedIntegers);
                        mergeResult.setGeneralizedState(((LLVMHeuristicState)mergeResult.getGeneralizedState()).setValue((LLVMHeuristicVariable)lastVar, lastValue));
                        return new LLVMComplexMemoryInvariant(termFactory.constant(first), lastVar, new LLVMAdditiveChange(change,sortedType), type);
                    } catch (TooExpensiveException e) {
                        // do nothing (so last is null)
                    }
                } 
            }
        }
        if (bigger.subList(1,bigger.size()).equals(smaller)) {
            // smaller =   [b]
            // bigger  = [a,b]
            // => if varOfInst values are a and b, we have found an invariant Inv(var..b;+change).
            for (Map.Entry<LLVMHeuristicVariable,Pair<BigInteger,BigInteger>> var : varOfInst.entrySet()) {
                BigInteger varOf = var.getValue().x;
                BigInteger varInst = var.getValue().y;
                BigInteger firstValueOf;
                BigInteger firstValueInst;
                if (ofIsSmaller) {
                    firstValueOf = smaller.get(0);
                    firstValueInst = bigger.get(0);
                } else {
                    firstValueInst = smaller.get(0);
                    firstValueOf = bigger.get(0);
                }
                if (varOf.equals(firstValueOf) && varInst.equals(firstValueInst)) {
                    return new LLVMComplexMemoryInvariant(var.getKey(), termFactory.constant(last), new LLVMAdditiveChange(change,sortedType), type);
                } else {
                    LLVMSimpleTerm smallerFirstVar = termFactory.constant(smaller.get(0));
                    LLVMSimpleTerm biggerFirstVar = termFactory.constant(bigger.get(0));
                    LLVMSymbolicVariable firstVar = null;
                    try {
                        if (ofIsSmaller) {
                            firstVar = mergeResult.mergeRefs(biggerFirstVar, smallerFirstVar, instIsNewerState);
                        } else {
                            firstVar = mergeResult.mergeRefs(smallerFirstVar, biggerFirstVar, instIsNewerState);
                        }
                        boolean unsigned = type.isPointerType();
                        LLVMValue firstValue = type.getInitializedIntValue(unsigned, mergeResult.getGeneralizedState().getStrategyParamters().useBoundedIntegers);
                        mergeResult.setGeneralizedState(((LLVMHeuristicState)mergeResult.getGeneralizedState()).setValue((LLVMHeuristicVariable)firstVar, firstValue));
                        return new LLVMComplexMemoryInvariant(firstVar, termFactory.constant(last), new LLVMAdditiveChange(change,sortedType), type);
                    } catch (TooExpensiveException e) {
                        // do nothing (so last is null)
                    }
                }
            }
        }
        // TODO add case where all values are the same, e.g. [0] and [0,0]
        return new LLVMComplexMemoryInvariant(null, null, new LLVMAdditiveChange(null,sortedType), type);
    }
    
    public BigInteger deduceLowerBoundForFirst(BigInteger lowerLength) {
        // if this is (v..0;-1) of length >= 3, a lower bound for v is 2
        if (this.additiveChange.getLinearRate() != null && this.additiveChange.getLinearRate().compareTo(BigInteger.ZERO) < 0) {
            if (this.lastValue instanceof LLVMHeuristicConstRef) {
                // return last - (change * (lowerLength - 1))
                BigInteger last = ((LLVMHeuristicConstRef)this.lastValue).getIntegerValue();
                BigInteger lowerLengthMinusOne = lowerLength.subtract(BigInteger.ONE);
                BigInteger mul = this.additiveChange.getLinearRate().multiply(lowerLengthMinusOne);
                BigInteger res = last.subtract(mul);
                return res;
            }
        }
        // special case for pointers: if lowerLength > 1, the first pointer is not null
        if (this.type.isPointerType() && this.type.getThisAsPointerType().pointsToStruct() && lowerLength.compareTo(BigInteger.ONE) > 0) {
            return BigInteger.ONE;
        }
        return null;
    }
    
    public BigInteger deduceLowerBoundForLength(BigInteger lowerFirst) {
        if (this.additiveChange.getLinearRate() == null) {
            if (this.lastValue instanceof LLVMHeuristicConstRef) {
                BigInteger last = ((LLVMHeuristicConstRef)this.lastValue).getIntegerValue();
                if (last.compareTo(lowerFirst) < 0) {
                    return BigInteger.valueOf(2);
                }
            }
        } else {
            // if this is (v..0;-1) with v >= 2, a lower bound for the length is 3.
            if (this.lastValue instanceof LLVMHeuristicConstRef) {
                // return 1 - ceil((lowerFirst - last)/change)
                BigInteger last = ((LLVMHeuristicConstRef)this.lastValue).getIntegerValue();
                BigInteger lowerFirstMinusLast = lowerFirst.subtract(last);
                BigInteger[] divAndRem = lowerFirstMinusLast.divideAndRemainder(this.additiveChange.getLinearRate());
                BigInteger ceil = divAndRem[0];
                if (!divAndRem[1].equals(BigInteger.ZERO)) {
                    ceil = ceil.add(BigInteger.ONE);
                }
                BigInteger res = BigInteger.ONE.subtract(ceil);
                return res;
            }
        }
        return BigInteger.ZERO;
    }
    
    public BigInteger deduceUpperBoundForFirst(BigInteger lowerLength) {
        // if this is (v..0;1) of length >= 3, an upper bound for v is -2
        if (this.additiveChange.getLinearRate() != null && this.additiveChange.getLinearRate().compareTo(BigInteger.ZERO) > 0) {
            if (this.lastValue instanceof LLVMHeuristicConstRef) {
                // return last - (change * (lowerLength - 1))
                BigInteger last = ((LLVMHeuristicConstRef)this.lastValue).getIntegerValue();
                BigInteger lowerLengthMinusOne = lowerLength.subtract(BigInteger.ONE);
                BigInteger mul = this.additiveChange.getLinearRate().multiply(lowerLengthMinusOne);
                BigInteger res = last.subtract(mul);
                return res;
            }
        }
        return null;
    }
    
    @Override
    public boolean equals(Object other) {
        if (other == null) {
            return false;
        }
        if (other instanceof LLVMComplexMemoryInvariant) {
            if (this.firstValue == null || ((LLVMComplexMemoryInvariant) other).firstValue == null) {
                if (this.firstValue != null || ((LLVMComplexMemoryInvariant) other).firstValue != null) {
                    return false;
                }
            } else if (!((LLVMComplexMemoryInvariant) other).firstValue.equals(this.firstValue)) {
                return false;
            }
            if (this.lastValue == null || ((LLVMComplexMemoryInvariant) other).lastValue == null) {
                if (this.lastValue != null || ((LLVMComplexMemoryInvariant) other).lastValue != null) {
                    return false;
                }
            } else if (!((LLVMComplexMemoryInvariant) other).lastValue.equals(this.lastValue)) {
                return false;
            }
            if (this.additiveChange == null || ((LLVMComplexMemoryInvariant) other).additiveChange == null) {
                if (this.additiveChange != null || ((LLVMComplexMemoryInvariant) other).additiveChange != null) {
                    return false;
                }
            } else if (!((LLVMComplexMemoryInvariant) other).additiveChange.equals(this.additiveChange)) {
                return false;
            }
            if (this.type == null || ((LLVMComplexMemoryInvariant) other).type == null) {
                if (this.type != null || ((LLVMComplexMemoryInvariant) other).type != null) {
                    return false;
                }
            } else if (!((LLVMComplexMemoryInvariant) other).type.equals(this.type)) {
                return false;
            }
            return true;
        }
        return false;
    }
    
    public LLVMAdditiveChange getChange() {
        return this.additiveChange;
    }
    
    public LLVMSimpleTerm getFirstValue() {
        return this.firstValue;
    }
    
    public LLVMSimpleTerm getLastValue() {
        return this.lastValue;
    }
    
    public LLVMType getType() {
        return this.type;
    }

    @Override
    public Set<LLVMSymbolicVariable> getUsedReferences() {
        Set<LLVMSymbolicVariable> res = new LinkedHashSet<LLVMSymbolicVariable>();
        if (this.firstValue != null) {
            res.addAll(this.firstValue.getVariables());
        }
        if (this.lastValue != null) {
            res.addAll(this.lastValue.getVariables());
        }
        return res;
    }
    
    public LLVMComplexMemoryInvariant havoc(LLVMSimpleTerm first, LLVMSimpleTerm last, LLVMSortedType sorted) {
        return new LLVMComplexMemoryInvariant(first, last, new LLVMAdditiveChange(null, sorted), this.type);
    }

    @Override
    public boolean isSimple() {
        return false;
    }

    @Override
    public Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> joinInvariant(
        LLVMAbstractState state,
        LLVMMemoryInvariant other,
        Abortion aborter
    ) {
        if (other instanceof LLVMSimpleMemoryInvariant) {
            LLVMSimpleMemoryInvariant simple = (LLVMSimpleMemoryInvariant) other;
            // if this = (v1..v2;x) and other = v3, and there is a relation v3 = v2 + x,
            // then create (v1..v3;x)
            LLVMSimpleTerm v1 = this.getFirstValue();
            LLVMSimpleTerm v2 = this.getLastValue();
            LLVMSimpleTerm v3 = simple.getPointedToValue();
            LLVMSimpleTerm x = null;
            LLVMTerm v2PlusX = null;
            LLVMRelation rel = null;
            if (this.getChange().getLinearRate() != null) {
                x = state.getRelationFactory().getTermFactory().constant(this.getChange().getLinearRate());
            }
            if (x != null) {
                v2PlusX = state.getRelationFactory().getTermFactory().add(v2, x);
            }
            if (v2PlusX != null) {
                rel = state.getRelationFactory().createRelation(IntegerRelationType.EQ, v3, v2PlusX);
            }
            LLVMComplexMemoryInvariant newInv = null;
            if (rel != null && state.checkRelation(rel, aborter).x) {
                newInv = new LLVMComplexMemoryInvariant(v1, v3, this.getChange(), this.getType());
            }
            if (newInv == null) {
                if (this.additiveChange.getSortedType() != LLVMSortedType.UNSORTED) {
                    LLVMSortedType sortedType = LLVMSortedType.UNSORTED;
                    if (this.additiveChange.getSortedType() == LLVMSortedType.ASCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThan(v2, v3), aborter).x) {
                            sortedType = LLVMSortedType.ASCENDING;
                        } else if (state.checkRelation(state.getRelationFactory().lessThanEquals(v2, v3), aborter).x) {
                            sortedType = LLVMSortedType.NONDESCENDING;
                        }
                    } else if (this.additiveChange.getSortedType() == LLVMSortedType.DESCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThan(v3, v2), aborter).x) {
                            sortedType = LLVMSortedType.DESCENDING;
                        } else if (state.checkRelation(state.getRelationFactory().lessThanEquals(v3, v2), aborter).x) {
                            sortedType = LLVMSortedType.NONASCENDING;
                        }
                    } else if (this.additiveChange.getSortedType() == LLVMSortedType.NONASCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThanEquals(v3, v2), aborter).x) {
                            sortedType = LLVMSortedType.NONASCENDING;
                        }
                    } else if (this.additiveChange.getSortedType() == LLVMSortedType.NONDESCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThanEquals(v2, v3), aborter).x) {
                            sortedType = LLVMSortedType.NONDESCENDING;
                        }
                    }
                    newInv = this.havoc(v1, v3, sortedType);
                } else {
                    newInv = this.havoc(v1, v3, LLVMSortedType.UNSORTED);
                }
            }
            return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(newInv, state);
        }
        if (this.equals(other)) {
            return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(
                new LLVMComplexMemoryInvariant(this.firstValue, this.lastValue, this.additiveChange, this.type),
                state
            );
        }
        return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(null, state);
    }

    @Override
    public Pair<LLVMSimpleTerm, LLVMAbstractState> load(LLVMAbstractState state, LLVMSimpleTerm ptr,
            LLVMType targetType, boolean unsigned, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public LLVMMemoryInvariant replaceReference(LLVMSimpleTerm old_ref, LLVMSimpleTerm new_ref) {
        if (this.firstValue != null && this.firstValue.equals(old_ref)) {
            if (this.lastValue != null && this.lastValue.equals(old_ref)) {
                return new LLVMComplexMemoryInvariant(new_ref, new_ref, this.additiveChange, this.type);
            } else {
                return new LLVMComplexMemoryInvariant(new_ref, this.lastValue, this.additiveChange, this.type);
            }
        } else if (this.lastValue != null && this.lastValue.equals(old_ref)) {
            return new LLVMComplexMemoryInvariant(this.firstValue, new_ref, this.additiveChange, this.type);
        }
        return this;
    }

    @Override
    public LLVMMemoryInvariant replaceReferences(Map<? extends LLVMSimpleTerm, ? extends LLVMSimpleTerm> replacements) {
        LLVMComplexMemoryInvariant res = this;
        if (replacements.containsKey(this.firstValue)) {
            res = (LLVMComplexMemoryInvariant) res.replaceReference(res.firstValue, replacements.get(res.firstValue));
        }
        if (replacements.containsKey(this.lastValue)) {
            res = (LLVMComplexMemoryInvariant) res.replaceReference(res.lastValue, replacements.get(res.lastValue));
        }
        return res;
    }

    @Override
    public String toString() {
        return "Inv(" + this.type + ":"
                + (this.firstValue == null ? "?" : this.firstValue) + ".."
                + (this.lastValue == null ? "?" : this.lastValue) + ";"
                + (this.additiveChange.toString()) + ")";
    }

    @Override
    public boolean usesReference(LLVMSimpleTerm other) {
        if (firstValue != null) {
            if (lastValue != null) {
                return firstValue.getVariables().contains(other) || lastValue.getVariables().contains(other);
            } else {
                return firstValue.getVariables().contains(other);
            }
        } else {
            if (lastValue != null) {
                return lastValue.getVariables().contains(other);
            } else {
                return false;
            }
        }
    }

    @Override
    public Pair<Boolean, ? extends LLVMAbstractState> mayShareWith(LLVMMemoryInvariant other, LLVMAbstractState state,
            Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

}
