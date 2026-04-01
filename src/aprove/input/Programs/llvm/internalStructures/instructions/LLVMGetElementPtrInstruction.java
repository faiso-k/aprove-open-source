package aprove.input.Programs.llvm.internalStructures.instructions;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class represent getelementptr llvm instructions. A complete description can be found on
 * http://llvm.org/docs/LangRef.html#i_getelementptr, and useful help on understanding it is found
 * on http://llvm.org/docs/GetElementPtr.html.
 *
 * The general idea is to perform pointer arithmetic, without actually touching the memory. Hence,
 * a "base" pointer is provided, and then a list of (type, value) index tuples is given, where value
 * is either an integer constant or a program variable with some integer value. The result is then
 * computed by turning the (type,value) tuples into numbers which can be added to the base pointer.
 *
 * @author Janine, cryingshadow, Jera Hensel
 */
public class LLVMGetElementPtrInstruction extends LLVMAssignmentInstruction {

//    /**
//     * Tries to infer useful knowledge for the reference corresponding to the computed result.
//     * @param newState The state to add the new knowledge to.
//     * @param pointerRef The original pointer's reference.
//     * @param result The computed result.
//     * @param resultType The type of the result.
//     * @param addedRefList The list of references and multipliers used to compute the result.
//     * @param offset A BigInteger indicating the exact offset from the original pointer if it is known (is null
//     *               otherwise).
//     * @param params Strategy parameters.
//     * @return The new state, a reference for the result, its corresponding association offset, and relations
//     *         representing the inferred knowledge about this reference.
//     */
//    private static GEPKnowledge inferKnowledgeForResult(
//        LLVMAbstractState newState,
//        LLVMHeuristicVariable pointerRef,
//        LLVMValue result,
//        BasicType resultType,
//        List<Pair<LLVMHeuristicVariable, LiteralBoundedInt>> addedRefList,
//        BigInteger offset,
//        LLVMParameters params
//    ) {
//        // TODO check for constant?
//        LLVMAbstractState res = newState;
//        IntegerRelationSet relations = new IntegerRelationSet(newState.getRelations());
//        Collection<LLVMStateChangeInformation> edgeInformation = new LinkedHashSet<LLVMStateChangeInformation>();
//        if (offset != null && offset.equals(BigInteger.ZERO)) {
//            // If we added nothing, resulting reference is just the pointer.
//            return new GEPKnowledge(res, pointerRef, edgeInformation);
//        }
//        LLVMHeuristicVariable resRef = LLVMHeuristicVarRef.createNewRef();
//        // Build a relation expression that matches the value we are computing:
//        LLVMRelation relExprMatchingGEPComputation =
//            LLVMRelation.createAdditionRelation((LLVMHeuristicVarRef)resRef, (LLVMHeuristicVarRef)pointerRef, addedRefList);
//        // Maybe we already have a name for this expression:
//        LLVMHeuristicVariable oldRef =
//            LLVMHeuristicExpressionUtils.findReferenceForExpression(
//                res.getValues(),
//                relations,
//                relExprMatchingGEPComputation.getEqualExpression(resRef)
//            );
//        if (oldRef == null) {
//            // Add value for the result to the state:
//            res = res.setValue(resRef, result);
//            Pair<LLVMAbstractState, IntegerRelationSet> knowledge =
//                res.addRelation(relExprMatchingGEPComputation, params);
//            res = knowledge.x;
//            edgeInformation.add(relExprMatchingGEPComputation);
//        } else {
//            // we already have a reference for the result
//            resRef = oldRef;
////            if (oldRef instanceof LLVMVarRef) {
////                edgeInformation.add(
////                    Relation.createAdditionRelation((LLVMVarRef)oldRef, (LLVMVarRef)pointerRef, addedRefList)
////                );
////            }
//        }
//        return new GEPKnowledge(res, resRef, edgeInformation);
//    }

    /**
     * Determines the behavior in case the resulting address is not in bounds. If true, a trap value
     * (undef) will be returned. Otherwise, address computation is performed without checking for bounds or overflows,
     * so the resulting pointer may well point to some non-allocated memory (but this will only produce an error or
     * undefined behavior if this pointer is used to load or store information from or to the heap).
     */
    private final boolean inbounds;

    /**
     * The index tuples, containing a type and a value.
     */
    private final ImmutableList<LLVMLiteral> indices;

    /**
     * The base pointer, which is used as basis for our address computation.
     */
    private final LLVMLiteral pointerLiteral;

    /**
     * @param id The variable to be assigned.
     * @param pLiteral The pointer to the first object.
     * @param setInbounds Poison values for not in bounds addresses enabled?
     * @param idxs The indices.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMGetElementPtrInstruction(
        LLVMVariableLiteral id,
        LLVMLiteral pLiteral,
        boolean setInbounds,
        ImmutableList<LLVMLiteral> idxs,
        int debugLine
    ) {
        super(id, debugLine);
        this.pointerLiteral = pLiteral;
        this.inbounds = setInbounds;
        this.indices = idxs;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.pointerLiteral);
        for (LLVMLiteral ind : this.indices) {
            LLVMInstruction.collectVariable(vars, ind);
        }
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
        // TODO
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        if (Globals.useAssertions) {
            assert (this.pointerLiteral instanceof LLVMVariableLiteral) :
                "Constants should not occur as base for GEPs - at least this is not documented (node "
                + nodeNumber
                + ").";
        }
        // since the literal must be a variable, the corresponding simple term must be one, too
        final LLVMSymbolicVariable pointerRef =
            (LLVMSymbolicVariable)state.getSimpleTermForLiteral(this.pointerLiteral);
        final LLVMParameters params = state.getStrategyParamters();
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        /*
         * GEP does not check whether the base pointer is null - this is no problem for the instruction itself.
         * However, the returned pointer may not be used for LLVM objects (so only for objects which are managed
         * outside of LLVM). So we either need a special check that such a situation (computing an address from a null
         * pointer) cannot occur (current solution) or we would need a special pointer type for such DONOTUSE-pointers
         * which causes errors as soon as they are used for a load or store instruction. This would be the more precise
         * solution. However, it will probably make no real difference in practice as automatically compiled LLVM
         * programs won't contain this situation. So it is a weak TODO for now.
         */
        LLVMAbstractState newState = state;
        if (proveMemorySafety) {
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                newState.checkRelation(relationFactory.lessThan(termFactory.zero(), pointerRef), aborter);
            newState = check.y;
            if (!check.x) {
                // Not necessarily greater than zero => give up, since we cannot track the behavior of this pointer yet
                throw
                    new UnsupportedOperationException(
                        "We cannot handle GEP on null pointers, yet (node " + nodeNumber + ")."
                    );
            }
        }
        if (newState.isPossiblyTrapValue(pointerRef)) {
            throw new TrapValueException(nodeNumber);
        }
        // TODO we also get a trap value if any of the intermediate addresses is out of bounds if inbounds is set
        final LLVMPointerType pointerType = this.pointerLiteral.getType().getThisAsPointerType();
        boolean unsigned = false;
        if (state.getStrategyParamters().useBoundedIntegers) {
            unsigned = state.getModule().getAddressesToUnsignedBitvectorVariables().contains(pointerLiteral.getName());
        }
        // Check if we have to refine since pointerRef is the next pointer in the first element of a struct invariant of length 1 or bigger.
        // Only search for new struct invariants if there is an index != 0.
        for (LLVMLiteral index : this.indices) {
            if (!(index.toString().equals("0"))) {
                Set<LLVMSymbolicEvaluationResult> refRes =
                    newState.findAndRefineStructInvariant(
                        new LLVMMemoryRange(pointerRef, pointerRef, pointerType.getTargetType(), unsigned),
                        aborter
                    );
                if (refRes != null) {
                    assert(refRes.size()==2);
                    return refRes;
                }
            }
        }
        LLVMType resultType = pointerType;
        LLVMTerm resultTerm = pointerRef;
        boolean struct = false;
        if (pointerType.getTargetType() instanceof LLVMNamedType || pointerType.getTargetType().isStructureType()) {
            struct = true;
        }
        Set<AssociationAccess> accesses = new LinkedHashSet<AssociationAccess>();
        Pair<LLVMAssociationIndex, LLVMAbstractState> indexPair =
            newState.getAssociatedAllocationIndex(pointerRef, pointerType, true, aborter);
        newState = indexPair.y;
        LLVMAssociationIndex allocationIndex = indexPair.x;
        boolean trap = allocationIndex == null;
        boolean isStructPointer = state.isStructPointer(pointerRef);
        for (LLVMLiteral index : this.indices) {
            // determine resultType
            // TODO the manual says that except for the base pointer, no type we index into can be a pointer
            if (resultType.isPointerType()) {
                resultType = resultType.getThisAsPointerType().getTargetType();
            } else {
                if (index instanceof LLVMIntLiteral) {
                    resultType = resultType.getSubtype(index.toInt());
                } else {
                    resultType = resultType.getSubtype();
                }
            }
            BigInteger multiplier = BigInteger.valueOf(IntegerUtils.bitsToBytes(resultType.size()));
            if (struct) {
                // data is 8 aligned (for 64 bit architectures)
                if (multiplier.compareTo(BigInteger.valueOf(8)) < 0) {
                    multiplier = BigInteger.valueOf(8);
                }
            }
            LLVMSimpleTerm indexRef = newState.getSimpleTermForLiteral(index);
            if (indexRef instanceof LLVMSymbolicVariable) {
                if (newState.isPossiblyTrapValue(indexRef)) {
                    throw new TrapValueException(nodeNumber);
                }
            } else {
                if (Globals.useAssertions) {
                    assert (indexRef instanceof LLVMConstant) :
                        "Found simple term which is neither a variable nor a constant!";
                }
            }
            if (!trap) {
                final Pair<LLVMAssociationIndex, LLVMAbstractState> otherPair =
                    newState.getAssociatedAllocationIndex(
                        resultTerm,
                        new LLVMPointerType(resultType, newState.getModule().getPointerSize(), null),
                        true,
                        aborter
                    );
                newState = otherPair.y;
                if (allocationIndex != null) {
                    trap = !allocationIndex.x.equals(otherPair.x.x);
                }
            }
            // TODO multiplier = multiplier of first index, how do we know the type?
            if (multiplier.compareTo(BigInteger.ONE) == 0) {
                resultTerm = termFactory.add(resultTerm, indexRef);
            } else {
                resultTerm = termFactory.add(resultTerm, termFactory.mult(termFactory.constant(multiplier), indexRef));
            }
            accesses.add(new AssociationAccess(resultTerm, resultType));
        }
        boolean allocNewMemory = trap;
        boolean isStructNext = false;
        if (trap && newState instanceof LLVMHeuristicState) {
            if (((LLVMHeuristicState)newState).containsStructWithNextPointer(resultTerm, aborter)) {
                trap = false;
                isStructNext = true;
            }
        }
        allocNewMemory &= isStructNext;
        final String varName = this.getIdentifier().getName();
        final LLVMPointerType resultPointerType =
            new LLVMPointerType(resultType, newState.getModule().getPointerSize(), null);
        
        final Set<LLVMRelation> newRels = new LinkedHashSet<>();

        newState = newState.assign(varName, resultTerm, resultPointerType, newRels, aborter).incrementPC();
        final LLVMSymbolicVariable fresh = newState.getSymbolicVariableForProgramVariable(varName);
        // if this is a struct next pointer whose allocation index we "forgot" (while merging),
        // create a new allocation
        // Do not use if next has offset > 0 (i.e., it is not the first field of a struct)
//        if (allocNewMemory) {
//            BigInteger offset = BigInteger.valueOf(IntegerUtils.bitsToBytes(pointerType.getTargetType().size())).subtract(BigInteger.ONE);
//            // TODO is offset computed correctly?
//            res = LLVMAllocaInstruction.upperBound(res, fresh, resultPointerType, offset, newRels, aborter);
//            LLVMSymbolicVariable limitRef = termFactory.freshVariable();
//            LLVMRelation rel = relationFactory.createAdditionRelation(
//                                  limitRef,
//                                  fresh,
//                                  termFactory.constant(offset)
//                              );
//            res = res.addRelation(rel, aborter);
//            newRels.add(rel);
//            res = res.allocateMemoryAndAssociatePointer(
//                    fresh,
//                    limitRef,
//                    fresh,
//                    resultPointerType,
//                    true,
//                    newRels,
//                    aborter
//                );
//            indexPair = res.getAssociatedAllocationIndex(pointerRef, pointerType, true, aborter);
//            res = indexPair.y;
//            allocationIndex = indexPair.x;
//        }
        if (allocationIndex == null) {
            if (proveMemorySafety && this.inbounds) {
                accesses.add(new AssociationAccess(pointerRef, pointerType.getTargetType()));
                if (!isStructPointer && !isStructNext) {
                    newState = newState.putTrapValue(fresh, new InboundsTrap(accesses, null));
                }
            }
        } else {
            // try to infer association for new address
            LLVMAllocation allocation = newState.getAllocations().get(allocationIndex.x);
            Pair<Boolean, ? extends LLVMAbstractState> check =
                newState.checkRelation(relationFactory.lessThanEquals(allocation.x, fresh), aborter);
            newState = check.y;
            if (check.x) {
                check =
                    newState.checkRelation(
                        relationFactory.lessThanEquals(
                            termFactory.add(
                                fresh,
                                termFactory.constant(resultPointerType.toOffset())
                            ),
                            allocation.y
                        ),
                        aborter
                    );
                newState = check.y;
                if (check.x) {
                    newState = newState.associateAccess(fresh, resultPointerType, allocationIndex.x, newRels, aborter);
                    if (params.proveMemorySafety && this.inbounds && trap) {
                        newState = newState.putTrapValue(fresh, new InboundsTrap(accesses, allocationIndex.x));
                    }
                } else if (params.proveMemorySafety && this.inbounds) {
                    // one cell after allocated object is ok for GEP (and we only need the address of the first cell)
                    if (trap) {
                        newState = newState.putTrapValue(fresh, new InboundsTrap(accesses, allocationIndex.x));
                    } else {
                        check =
                            newState.checkRelation(
                                relationFactory.lessThanEquals(fresh, termFactory.add(allocation.y, termFactory.one())),
                                aborter
                            );
                        newState = check.y;
                        if (!check.x && !isStructNext) {
                            newState = newState.putTrapValue(fresh, new InboundsTrap(accesses, allocationIndex.x));
                        }
                    }
                }
            } else if (params.proveMemorySafety && this.inbounds && !isStructNext) {
                newState = newState.putTrapValue(fresh, new InboundsTrap(accesses, allocationIndex.x));
            }
        }
        /*
         * Try to merge heap ranges into bigger ones. To do so we enumerated all adjacent heap ranges and then
         * we check if the underlying invariants are compatible.
         */
        newState =
            newState.findAndCreateInvariantsForAccess(
                new LLVMMemoryRange(pointerRef, pointerRef, pointerType.getTargetType(), unsigned),
                aborter
            );
        // Only search for new struct invariants if there is an index != 0.
        for (LLVMLiteral index : this.indices) {
            if (!(index.toString().equals("0"))) {
                // If there exists a struct invariant for pointerRef but none for the pointed-to-value, find one.
                LLVMSymbolicEvaluationResult evalRes =
                    newState.findAndCreateStructInvariantForNext(
                        new LLVMMemoryRange(pointerRef, pointerRef, pointerType.getTargetType(), unsigned),
                        fresh,
                        aborter
                    );
                if (evalRes != null) {
                    newState = evalRes.x;
                    newRels.addAll(evalRes.y);
                }
            }
        }
        //TODO merge the newly created bigger invariants as well
        // TODO re-implement overflow checks for bounded integer case
        return
            Collections.singleton(
                new LLVMSymbolicEvaluationResult(newState, newRels)
            );
//        LLVMValue pointerValue = state.getValue(pointerRef);
//        if (pointerValue instanceof LLVMTrapValue) {
//        }
//        AbstractBoundedInt pointerVal = pointerValue.getThisAsAbstractBoundedInt();
//        // the offset from the original pointer - will be set to null if there is no exact value for the offset
//        BigInteger offset = BigInteger.ZERO;
//        // compute the resulting address and type
//        AbstractBoundedInt result = pointerVal;
//        BasicType resultType = this.pointerLiteral.getType();
//        // TODO we need special treatment of non-pointer types for GEP
//        ArrayList<Pair<LLVMHeuristicVariable, LiteralBoundedInt>> addedRefList =
//            new ArrayList<Pair<LLVMHeuristicVariable, LiteralBoundedInt>>();
//        for (BasicLiteral index : this.indices) {
//            // determine resultType
//            // TODO the manual says that except for the base pointer, no type we index into can be a pointer
//            if (resultType.isPointerType()) {
//                resultType = resultType.getThisAsPointerType().getTargetType();
//            } else {
//                if (index instanceof BasicInt) {
//                    resultType = resultType.getSubtype(index.toInt());
//                } else {
//                    resultType = resultType.getSubtype();
//                }
//            }
//            // TODO check whether this corresponds to the formula with type size of Janine's diploma thesis
//            // addresses are computed as units of 8 bits
//            LiteralBoundedInt multiplier =
//                AbstractBoundedInt.create(IntegerUtils.bitsToBytes(resultType.size()));
//            LLVMHeuristicVariable indexRef = state.getTermForLiteral(index);
//            addedRefList.add(new Pair<LLVMHeuristicVariable, LiteralBoundedInt>(indexRef, multiplier));
//            LLVMValue indexValue = state.getValue(indexRef);
//            if (indexValue instanceof LLVMTrapValue) {
//                throw new UndefinedBehaviorException("Accessing trap value at node " + nodeNumber + ".");
//            }
//            AbstractBoundedInt indexVal = indexValue.getThisAsAbstractBoundedInt();
//            final boolean useBoundedIntegers = params.useBoundedIntegers;
//            if (useBoundedIntegers) {
//                try {
//                    indexVal = indexVal.mul(multiplier, module.getPointerType(), false).x;
//                    indexVal =
//                        AbstractBoundedInt.create(
//                            indexVal.getLower(),
//                            indexVal.getUpper(),
//                            result.getMinLower(),
//                            result.getMaxUpper(),
//                            indexVal.getLowerCounter(),
//                            indexVal.getUpperCounter()
//                        );
//                    final Triple<AbstractBoundedInt, BigInteger, BigInteger> addResult =
//                        result.add(indexVal, module.getPointerType(), false);
//                    result = addResult.x;
//                    if (Globals.useAssertions) {
//                        assert (addResult.y == null && addResult.z == null) :
//                            "Overflow occurred in getelementptr instruction.";
//                    }
//                } catch (OverflowException e) {
//                    throw new IllegalStateException(
//                        "Overflow occurred in getelementptr instruction!"
//                    );
//                }
//            } else {
//                try {
//                    indexVal = indexVal.mul(multiplier, IntegerType.UNBOUND, false).x;
//                    result = result.add(indexVal, IntegerType.UNBOUND, false).x;
//                } catch (OverflowException e) {
//                        throw new IllegalStateException(
//                            "Overflow: This should not happen with IntegerType.UNBOUND (node "
//                            + nodeNumber
//                            + ")!"
//                        );
//                }
//            }
//            if (offset != null) {
//                if (indexVal.isIntLiteral()) {
//                    offset = offset.add(indexVal.getIntLiteralValue());
//                } else {
//                    offset = null;
//                }
//            }
//        }
//        // store the association offset for the new pointer
//        BigInteger targetOffset = BigInteger.valueOf(IntegerUtils.bitsToBytes(resultType.size()) - 1);
//        // the getelementptr instructions gives a pointer to the determined address => change type to pointer
//        resultType = new BasicPointerType(resultType, module.getPointerSize(), null);
//        // Create name for result:
//        String resVarName = this.getIdentifier().getName();
//        GEPKnowledge res =
//            GetElementPtrInstruction.inferKnowledgeForResult(
//                state,
//                pointerRef,
//                result,
//                resultType,
//                addedRefList,
//                offset,
//                params
//            );
//        // Set variable to the result value
//        LLVMAbstractState newState =
//            res.x.setProgramVariable(
//                resVarName,
//                res.y,
//                resultType
//            ).restrictToUsedReferences(state.getUsedReferences(true), params);
//        // after restriction, some relations in the state change information may not be implied anymore, so add them
//        // again
//        for (LLVMStateChangeInformation info : res.z) {
//            if (info instanceof LLVMRelation) {
//                newState = newState.addRelation((LLVMRelation)info, params).x;
//            }
//        }
//        Integer index = newState.getAssociations().get(pointerRef);
//        if (index == null) {
//            if (params.proveMemorySafety && this.inbounds) {
//                // we have a trap value
//                newState =
//                    newState.putTrapValue(
//                        res.y,
//                        newState.getValue(res.y),
//                        new ImmutablePair<LLVMHeuristicVariable, BigInteger>(
//                            pointerRef,
//                            BigInteger.valueOf(
//                                IntegerUtils.bitsToBytes(
//                                    ((BasicPointerType)this.pointerLiteral.getType()).getTargetType().size()
//                                ) - 1
//                            )
//                        )
//                    );
//            }
//        } else {
//            // try to infer association for new address
//            ImmutablePair<LLVMHeuristicVariable, LLVMHeuristicVariable> pair = newState.getAllocations().get(index);
//            if (
//                IntegerUtils.truthValueOfRelation(
//                    newState,
//                    pair.x,
//                    IntegerRelationType.LE,
//                    res.y,
//                    true,
//                    params
//                ) == YNM.YES
//            ) {
//                // resulting pointer is in lower bounds
//                if (
//                    IntegerUtils.truthValueOfRelation(
//                        newState,
//                        IntegerUtils.upperAddress(res.y, targetOffset),
//                        IntegerRelationType.LE,
//                        pair.y,
//                        true,
//                        params
//                    ) == YNM.YES
//                ) {
//                    // resulting pointer is in upper bounds
//                    newState = newState.associateAccess(res.y, targetOffset, index);
//                } else if (params.proveMemorySafety && this.inbounds) {
//                    // one cell after allocated object is ok for GEP (and we only need the address of the first cell)
//                    if (
//                        IntegerUtils.truthValueOfRelation(
//                            newState,
//                            res.y,
//                            IntegerRelationType.LE,
//                            LLVMOperation.create(
//                                ArithmeticOperationType.ADD,
//                                pair.y,
//                                LLVMHeuristicTermFactory.ONE
//                            ),
//                            true,
//                            params
//                        ) != YNM.YES
//                    ) {
//                        throw new UndefinedBehaviorException(
//                            "We left allocated memory on inbounds GEP (above upper bound) - poison value will lead to "
//                            + "undefined behavior (node "
//                            + nodeNumber
//                            + ")!"
//                        );
//                    }
//                }
//            } else if (params.proveMemorySafety && this.inbounds) {
//                throw new UndefinedBehaviorException(
//                    "We left allocated memory on inbounds GEP (below lower bound) - poison value will lead to "
//                    + "undefined behavior (node "
//                    + nodeNumber
//                    + ")!"
//                );
//            }
//        }
//        // increment program counter and unset refinement flag
//        return new Pair<LLVMAbstractState, Collection<LLVMStateChangeInformation>>(
//            newState.incrementPC(),
//            res.z
//        );
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }
    
    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = getelementptr "));
        res.append(eu.tttext(this.pointerLiteral.toString()));
        for (LLVMLiteral index : this.indices) {
            res.append(eu.tttext(", "));
            res.append(eu.tttext(index.toString()));
        }
        return res.toString();
    }

    @Override
    public Set<String> getInterestingVariables() {
        return Collections.emptySet();
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("GetElementPtrInstr ");
        strBuilder.append(" indentifier: " + this.getIdentifier());
        strBuilder.append(" ptrType: " + this.pointerLiteral.getType());
        strBuilder.append(" ptrLiteral: " + this.pointerLiteral);
        strBuilder.append(" indices: (");
        boolean first = true;
        for (LLVMLiteral index : this.indices) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + index.toDebugString());
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder strBuilder = new StringBuilder(this.getIdentifier().toDOTString() + " = getelementptr ");
        strBuilder.append(this.pointerLiteral.toDOTString());
        for (LLVMLiteral index : this.indices) {
            strBuilder.append(", " + index);
        }
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder(this.getIdentifier() + " = getelementptr ");
        strBuilder.append(this.pointerLiteral);
        for (LLVMLiteral index : this.indices) {
            strBuilder.append(", " + index);
        }
        return strBuilder.toString();
    }

//    /**
//     * Triple of an abstract state, a reference, and some state change information.
//     * @author cryingshadow
//     * @version $Id$
//     */
//    private static class GEPKnowledge
//    extends Triple<LLVMAbstractState, LLVMHeuristicVariable, Collection<LLVMStateChangeInformation>> {
//
//        /**
//         * @param state The state component.
//         * @param ref The reference component.
//         * @param changeInfo The state change information component.
//         */
//        public GEPKnowledge(
//            LLVMAbstractState state,
//            LLVMHeuristicVariable ref,
//            Collection<LLVMStateChangeInformation> changeInfo
//        ) {
//            super(state, ref, changeInfo);
//        }
//
//    }

    /**
     * Memory accesses that need to be associated.
     * @author cryingshadow
     * @version $Id$
     */
    private static class AssociationAccess extends ImmutablePair<LLVMTerm, LLVMType> {

        /**
         * @param x The term describing the start address of the memory access.
         * @param y The target type of the memory access.
         */
        public AssociationAccess(LLVMTerm x, LLVMType y) {
            super(x, y);
        }

    }

    /**
     * Trap condition for inbounds trap values.
     * @author cryingshadow
     * @version $Id$
     */
    private static class InboundsTrap implements LLVMTrapCondition {

        /**
         * The index of the allocation to which the accesses need to be associated. Null if this is not fixed.
         */
        private final Integer allocationIndex;

        /**
         * The memory accesses which need to be associated to the same allocation.
         */
        private final ImmutableSet<AssociationAccess> toAssociate;

        /**
         * @param toAssociateParam The memory accesses to be associated to the same allocation.
         * @param index The index of the allocation to which the accesses need to be associated. Null if this is not
         *              fixed.
         */
        public InboundsTrap(Set<AssociationAccess> toAssociateParam, Integer index) {
            this.toAssociate = ImmutableCreator.create(toAssociateParam);
            this.allocationIndex = index;
        }

        @Override
        public InboundsTrap applySubstitution(Substitution sigma) {
            Set<AssociationAccess> newToAssociate = new LinkedHashSet<AssociationAccess>();
            for (AssociationAccess access : this.toAssociate) {
                newToAssociate.add(
                    new AssociationAccess((LLVMTerm)access.x.applySubstitution(sigma), access.y)
                );
            }
            return new InboundsTrap(newToAssociate, this.allocationIndex);
        }

        @Override
        public boolean equals(Object o) {
            if (o instanceof InboundsTrap) {
                InboundsTrap trap = (InboundsTrap)o;
                if (this.allocationIndex == null) {
                    if (trap.allocationIndex != null) {
                        return false;
                    }
                } else if (!this.allocationIndex.equals(trap.allocationIndex)) {
                    return false;
                }
                return this.toAssociate.equals(trap.toAssociate);
            }
            return false;
        }

        @Override
        public Set<LLVMSymbolicVariable> getVariables() {
            Set<LLVMSymbolicVariable> res = new LinkedHashSet<LLVMSymbolicVariable>();
            for (AssociationAccess access : this.toAssociate) {
                res.addAll(access.x.getVariables());
            }
            return res;
        }

        @Override
        public int hashCode() {
            return (this.allocationIndex == null ? 0 : this.allocationIndex) * 3 + this.toAssociate.hashCode() * 7;
        }

        @Override
        public Pair<Boolean, LLVMAbstractState> resolved(LLVMAbstractState state, Abortion aborter) {
            if (this.toAssociate.isEmpty()) {
                return new Pair<Boolean, LLVMAbstractState>(true, state);
            }
            final Integer index;
            AssociationAccess firstAccess = null;
            LLVMAbstractState newState = state;
            if (this.allocationIndex == null) {
                firstAccess = this.toAssociate.iterator().next();
                final Pair<LLVMAssociationIndex, LLVMAbstractState> newIndex =
                    newState.getAssociatedAllocationIndex(
                        firstAccess.x,
                        new LLVMPointerType(firstAccess.y, newState.getModule().getPointerSize(), null),
                        true,
                        aborter
                    );
                newState = newIndex.y;
                index = newIndex.x == null ? null : newIndex.x.x;
            } else {
                index = this.allocationIndex;
            }
            if (index == null) {
                return new Pair<Boolean, LLVMAbstractState>(false, newState);
            }
            for (AssociationAccess association : this.toAssociate) {
                if (association == firstAccess) {
                    continue;
                }
                final Pair<LLVMAssociationIndex, LLVMAbstractState> otherIndex =
                    newState.getAssociatedAllocationIndex(
                        association.x,
                        new LLVMPointerType(association.y, newState.getModule().getPointerSize(), null),
                        true,
                        aborter
                    );
                newState = otherIndex.y;
                if (otherIndex.x == null || !index.equals(otherIndex.x.x)) {
                    return new Pair<Boolean, LLVMAbstractState>(false, newState);
                }
            }
            return new Pair<Boolean, LLVMAbstractState>(true, newState);
        }

    }

}
