package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of storing values to an array.
 * @author Marc Brockschmidt
 */
public class ArrayAccess extends OpCode {
    /**
     * Type of the operand to be stored.
     */
    private final OperandType operandType;

    /**
     * Direction of access (either read or write).
     */
    private final FieldAccessRW readWriteType;

    /**
     * @param type Type of the operand to be stored into/read from the array
     * @param rw Direction of access (either read or write).
     */
    public ArrayAccess(final OperandType type, final FieldAccessRW rw) {
        this.operandType = type;
        this.readWriteType = rw;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        //No refinement needed, we have a split result:
        final SplitResult splitResult = s.getSplitResult();
        if (splitResult != null) {
            if (splitResult instanceof ArrayAccessSplitResult) {
                final ArrayAccessSplitResult res = (ArrayAccessSplitResult) splitResult;
                final Boolean needsArrayStoreException = res.needsArrayStoreException();
                if (needsArrayStoreException != null
                    && needsArrayStoreException.booleanValue()
                    && ObjectRefinement.forInitialization(Important.ARRAYSTORE_EXC, s, out))
                {
                    return true;
                }
                final Boolean needsIOOBException = res.needsIOOBException();
                if (needsIOOBException != null
                    && needsIOOBException.booleanValue()
                    && ObjectRefinement.forInitialization(Important.ARRAYINDEXOOB_EXC, s, out))
                {
                    return true;
                }
            }
            return false;
        }
        //Retrieve the references from the stack:
        final AbstractVariableReference arrayRef;
        final AbstractVariableReference indexRef;
        final AbstractVariableReference valueRef;
        if (this.readWriteType == FieldAccessRW.WRITE) {
            valueRef = s.getCurrentStackFrame().getOperandStack().peek(0);
            indexRef = s.getCurrentStackFrame().getOperandStack().peek(1);
            arrayRef = s.getCurrentStackFrame().getOperandStack().peek(2);
        } else {
            valueRef = null;
            indexRef = s.getCurrentStackFrame().getOperandStack().peek(0);
            arrayRef = s.getCurrentStackFrame().getOperandStack().peek(1);
        }

        // make sure we are not dealing with null
        if (ObjectRefinement.forExistence(arrayRef, s, out)) {
            return true;
        }
        if (arrayRef.isNULLRef()) {
            return ObjectRefinement.forInitialization(Important.NPE_EXC, s, out);
        }

        // provide the array length:
        if (ArrayRefinement.forArrayRealization(arrayRef, s, out)) {
            return true;
        }

        //Get the actual values:
        final AbstractVariable aA = s.getAbstractVariable(arrayRef);
        final Array array = (Array) aA;
        final AbstractVariable aI = s.getAbstractVariable(indexRef);
        final AbstractInt index = (AbstractInt) aI;
        final AbstractInt arrayLength = (AbstractInt) s.getAbstractVariable(array.getLength());

        //See if we need to refine or split for the index:
        final boolean indexGEZero = index.isNonNegative();
        final boolean indexLTLength =
            AbstractInt.computeComparisonResult(IntegerRelationType.LT, index, arrayLength, false, false);

        final boolean indexLTZero = index.isNegative();

        final boolean indexGELength =
            AbstractInt.computeComparisonResult(IntegerRelationType.GE, index, arrayLength, false, false);

        if (indexLTZero || indexGELength) {
            // we will have the case where we throw an AIOOBE
            if (ObjectRefinement.forInitialization(Important.ARRAYINDEXOOB_EXC, s, out)) {
                return true;
            }
        }

        /*
         * If this is set, we cannot decide/refine enough, so index >= arrayLength could both be true and false.
         * Therefore, we need to split (one case throws the IOOBE).
         */
        boolean splitForIOOBE;

        if ((indexGEZero && indexLTLength) || indexLTZero || indexGELength) {
            // information guarantees that the index either is in the bounds or is out of the bounds
            splitForIOOBE = false;
        } else {
            /*
             * OK, we need to refine. If index wasn't >= 0, we should
             * split off the negative part.
             */
            if (!indexGEZero) {
                final Collection<Pair<AbstractInt, AbstractInt>> smallerZeroResults =
                    IntegerRefinement.forIntegerRelation(index, AbstractInt.getZero(), IntegerRelationType.LT);
                assert (smallerZeroResults != null) : "Refinement wrt. 0 should always work!";
                assert (smallerZeroResults.size() > 1) : "Integer refinement with one successor ... sucks!";
                for (final Pair<AbstractInt, AbstractInt> refResult : smallerZeroResults) {
                    final AbstractInt newIndex = refResult.x;
                    if (Globals.useAssertions) {
                        assert (refResult.y.isZero()) : "Integer refinement changed constant!";
                    }
                    final State newState = s.clone();
                    final AbstractVariableReference newIndexRef =
                        newState.createReferenceAndAdd(newIndex, OperandType.INTEGER);
                    newState.replaceReference(indexRef, newIndexRef);
                    out.add(new Pair<State, EdgeInformation>(newState, new RefinementEdge(indexRef, newIndexRef)));
                }
                return true;
            }

            /*
             * Now we know index >= 0, but have no information whether
             * index <= length holds. Continue with refining the upper bound of
             * the index.
             */
            final Collection<Pair<AbstractInt, AbstractInt>> greaterLengthResults =
                IntegerRefinement.forIntegerRelation(index, arrayLength, IntegerRelationType.GE);
            if (greaterLengthResults != null) {
                // it was possible to refine so that index >= arrayLength can be decided
                assert (greaterLengthResults.size() > 1) : "Integer refinement with one successor ... sucks!";
                for (final Pair<AbstractInt, AbstractInt> refResult : greaterLengthResults) {
                    final AbstractInt newIndex = refResult.x;
                    final AbstractInt newArrayLength = refResult.y;
                    if (Globals.useAssertions) {
                        assert (newIndex.equals(index) || newArrayLength.equals(arrayLength)) : "Integer refinement changed both values";
                    }
                    final State newState = s.clone();
                    if (!newIndex.equals(index)) {
                        final AbstractVariableReference newIndexRef =
                            newState.createReferenceAndAdd(newIndex, OperandType.INTEGER);
                        newState.replaceReference(indexRef, newIndexRef);
                        out.add(new Pair<State, EdgeInformation>(newState, new RefinementEdge(indexRef, newIndexRef)));
                    }
                    if (!newArrayLength.equals(arrayLength)) {
                        final AbstractVariableReference newArrayLengthRef =
                            newState.createReferenceAndAdd(newArrayLength, OperandType.INTEGER);
                        newState.replaceReference(array.getLength(), newArrayLengthRef);
                        out.add(new Pair<State, EdgeInformation>(newState, new RefinementEdge(
                            array.getLength(),
                            newArrayLengthRef)));
                    }
                }
                return true;
            }
            // it was NOT possible to refine, so we do not know if index >= arrayLength holds or not

            // If we didn't return before reaching this point, we need to do a split for the index information:
            splitForIOOBE = true;
        }

        final AbstractType arrayType = s.getAbstractType(arrayRef);

        boolean isArray = arrayType.containsAbstractArrayParentType();
        if (!isArray) {
            for (FuzzyType t: arrayType.getPossibleClassesCopy()) {
                if (t.isArrayType()) {
                    isArray = true;
                }
            }
        }
        if (!isArray) {
            out.add(new Pair<State, EdgeInformation>(s.clone(), new FailedRefinementEdge(arrayRef + " is not an array")));
            return true;
        }

        boolean needsTypeSplit = false;
        //Now check if we need throw an ArrayStoreException:
        if (this.readWriteType == FieldAccessRW.WRITE
            && !this.operandType.isPrimitive()
            && !valueRef.isNULLRef()
            && !indexLTZero
            && !indexGELength)
        {
            needsTypeSplit = true;

            //Check if the values are compatible:
            final AbstractType valueType = s.getAbstractType(valueRef);

            final Boolean isStorageCompatible;
            if (valueType == null) {
                isStorageCompatible = false;
            } else {
                isStorageCompatible = valueType.isStorageCompatibleTo(arrayType, s.getClassPath(), s.getJBCOptions());
            }
            // maybe this is very easy?
            if (isStorageCompatible != null) {
                needsTypeSplit = false;
            }

            if (isStorageCompatible == null || !isStorageCompatible.booleanValue()) {
                if (ObjectRefinement.forInitialization(Important.ARRAYSTORE_EXC, s, out)) {
                    return true;
                }
            }

            /*
             * We may get around the type split if we do not have to deal with
             * an infinite number of possible types.
             */
            if (!arrayType.isAbstractJLO()
                && needsTypeSplit
                && !arrayType.containsAbstractArrayParentType()
                && valueType != null
                && !valueType.containsAbstractArrayParentType())
            {
                /*
                 * The type expansion is finite and doesn't cross array dimensions,
                 * so just let's check every concrete array type and do a type
                 * refinement. For that, we are a bit tricky and reduce the array
                 * type dimension by one, then do a usual refinement. As storage
                 * compatibility and assignment compatibility are basically the same.
                 */
                for (final FuzzyType t : arrayType.expand(s.getClassPath(), s.getJBCOptions())) {
                    // Check if for this single t, we are already done:
                    final AbstractType justT = new AbstractType(s.getClassPath(), t);
                    final Boolean thisTypeIsStorageCompatible =
                        valueType.isStorageCompatibleTo(justT, s.getClassPath(), s.getJBCOptions());

                    // Create a new reference for the new type, then set it:
                    final State expandedArrayTypeState = s.clone();
                    final AbstractVariable inst = expandedArrayTypeState.getAbstractVariable(arrayRef);
                    final AbstractVariableReference newRef;
                    if (inst != null) {
                        newRef = expandedArrayTypeState.createReferenceAndAdd(inst, OperandType.ARRAY);
                    } else {
                        newRef = AbstractVariableReference.create(arrayRef);
                    }
                    expandedArrayTypeState.replaceReference(arrayRef, newRef);
                    expandedArrayTypeState.setAbstractType(newRef, justT);

                    if (thisTypeIsStorageCompatible != null) {
                        /*
                         * We are done with this single type. Add the cloned
                         * state as a refinement result and continue with the
                         * next type.
                         */
                        out.add(new Pair<State, EdgeInformation>(expandedArrayTypeState, new RefinementEdge(
                            arrayRef,
                            newRef)));
                    } else {
                        // No, we can't. Do the value type refinement:
                        ObjectRefinement.forTypeOfInterest(
                            valueRef,
                            t.getEnclosedType(),
                            false,
                            expandedArrayTypeState,
                            out);
                    }
                }
                //We did the refine:
                return true;
            }
        }

        //Finish off by doing all needed splits:
        final Collection<Pair<SplitResult, Set<AbstractVariableReference>>> splitResults = new LinkedHashSet<>();
        if (splitForIOOBE) {
            if (needsTypeSplit) {
                final Set<AbstractVariableReference> refs = new LinkedHashSet<>();
                refs.add(arrayRef);
                refs.add(indexRef);

                // everything is OK, no exception is thrown
                splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                    false,
                    false), refs));

                // index is OK, but type is not
                splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                    false,
                    true), refs));

                // index is not OK
                splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                    true,
                    null), refs));
            } else {
                splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                    false,
                    null), Collections.singleton(indexRef)));
                splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                    true,
                    null), Collections.singleton(indexRef)));
            }
        } else if (needsTypeSplit) {
            splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                null,
                false), Collections.singleton(arrayRef)));
            splitResults.add(new Pair<SplitResult, Set<AbstractVariableReference>>(new ArrayAccessSplitResult(
                null,
                true), Collections.singleton(arrayRef)));
        }

        if (splitResults.isEmpty()) {
            return false;
        }
        for (final Pair<SplitResult, Set<AbstractVariableReference>> p : splitResults) {
            final State clone = s.clone();
            clone.setSplitResult(p.x);
            out.add(new Pair<State, EdgeInformation>(clone, new SplitEdge(p.y)));
        }

        return true;
    }

    /**
     * Generates a number of new states from a current state by refinement or
     * evaluation.
     * @param curState The old state
     * @return a number of successor states created by either evaluation,
     * refinement or splitting.
     */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State curState) {
        final State newState = curState.clone();

        //Retrieve the references from the stack:
        AbstractVariableReference arrayRef;
        final AbstractVariableReference indexRef;
        final AbstractVariableReference valueRef;
        if (this.readWriteType == FieldAccessRW.WRITE) {
            valueRef = newState.getCurrentStackFrame().getOperandStack().peek(0);
            indexRef = newState.getCurrentStackFrame().getOperandStack().peek(1);
            arrayRef = newState.getCurrentStackFrame().getOperandStack().peek(2);
        } else {
            valueRef = null;
            indexRef = newState.getCurrentStackFrame().getOperandStack().peek(0);
            arrayRef = newState.getCurrentStackFrame().getOperandStack().peek(1);
        }

        if (Globals.useAssertions) {
            assert !indexRef.pointsToLong() : "Index should be an int (no long)";
        }

        //Get values, do some sanity checks:
        final AbstractVariable aA = newState.getAbstractVariable(arrayRef);
        final AbstractVariable aI = newState.getAbstractVariable(indexRef);
        assert (aA instanceof Array || aA.isNULL()) : "Trying to access array, but variable "
            + arrayRef
            + " isn't an array";
        assert (aI instanceof AbstractInt) : "Trying to access array index, but variable "
            + indexRef
            + " isn't a number";

        //The NPE can be handled now, without further ado:
        if (aA.isNULL()) {
            OpCode.throwException(newState, NPE_EXC);
            return new Pair<>(newState, new MethodStartEdge());
        }
        final Array array = (Array) aA;
        final AbstractInt arrayLength = (AbstractInt) newState.getAbstractVariable(array.getLength());
        final AbstractInt index = (AbstractInt) aI;

        //Did we do a split?
        final ArrayAccessSplitResult splitRes = (ArrayAccessSplitResult) curState.getSplitResult();
        Boolean indexOutOfBounds = null;
        if (splitRes != null) {
            indexOutOfBounds = splitRes.needsIOOBException();
        }

        if (indexOutOfBounds == null) {
            final boolean indexLTZero = index.isNegative();
            final boolean indexGEZero = index.isNonNegative();
            // true => index < length
            final boolean indexLTLength =
                AbstractInt.computeComparisonResult(IntegerRelationType.LT, index, arrayLength, false, false);
            // true => index >= length
            final boolean indexGELength =
                AbstractInt.computeComparisonResult(IntegerRelationType.GE, index, arrayLength, false, false);
            if (indexLTZero || indexGELength) {
                indexOutOfBounds = Boolean.TRUE;
            } else if (indexGEZero && indexLTLength) {
                indexOutOfBounds = Boolean.FALSE;
            } else {
                assert (false) : "Trying to access array, but index "
                    + index
                    + " and length "
                    + arrayLength
                    + " haven't been refined enough";
                return null;
            }
        }

        //Now do the iOOB exception, if needed:
        if (indexOutOfBounds.booleanValue()) {
            OpCode.throwException(newState, ARRAYINDEXOOB_EXC);
            final MethodStartEdge methodStartEdge = new MethodStartEdge();

            // maybe we have some detailled information about the index?
            if (index.isNegative()) {
                final BigInteger upperBound = index.getUpper().getConstant();
                methodStartEdge.add(new JBCIntegerRelation(indexRef, IntegerRelationType.LE, upperBound));
            } else {
                /*
                 * During refinement we make sure that we always know whether
                 * index < 0 or index >= length holds. This also means we now
                 * know if we have index >= length or not.
                 */
                final boolean indexGELength =
                    AbstractInt.computeComparisonResult(IntegerRelationType.GE, index, arrayLength, false, false);
                if (indexGELength && index.getLower().isFinite()) {
                    final BigInteger lowerBound = index.getLower().getConstant();
                    methodStartEdge.add(new JBCIntegerRelation(indexRef, IntegerRelationType.GE, lowerBound));

                    /*
                     * Helpful for
                     *  length [0, x], index [x, ...
                     * or
                     *  length [0, x], index [y, ... (with y>x)
                     *  if the graph does not give information about x.
                     */
                    BigInteger min = lowerBound;
                    if (arrayLength.getUpper().isFinite()) {
                        min = min.min(arrayLength.getUpper().getConstant());
                    }
                    methodStartEdge.add(new JBCIntegerRelation(array.getLength(), IntegerRelationType.LE, min));
                } else {
                    methodStartEdge.add(new JBCIntegerRelation(indexRef, IntegerRelationType.GE, array.getLength()));
                }
            }
            return new Pair<>(newState, methodStartEdge);
        }

        final EvaluationEdge edge = new EvaluationEdge();
        //Don't do this for the random input stuff:
        if (!arrayRef.equals(curState.getStaticFields().get(ClassName.fromDotted("Random"), "args"))) {

            edge.add(new JBCIntegerRelation(indexRef, IntegerRelationType.LT, array.getLength()));
            /*
            if (index.getLower().isFinite()) {
                final BigInteger lowerBound = index.getLower().getConstant();
                edge.add(new IntegerRelation(indexRef, IntegerRelationType.GE,
                        lowerBound));
            } else {
                edge.add(new IntegerRelation(indexRef, IntegerRelationType.GE, 0));
            }
            if (index.getUpper().isFinite()) {
                final BigInteger upperBound = index.getUpper().getConstant();
                edge.add(new IntegerRelation(indexRef, IntegerRelationType.LE,
                        upperBound));
            } else {
                edge.add(new IntegerRelation(indexRef, IntegerRelationType.LT,
                        array.getLength()));
            }
            */
        }

        if (this.readWriteType == FieldAccessRW.WRITE) {
            return this.evalWrite(splitRes, newState, edge, array, arrayRef, indexRef, valueRef);
        }

        newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
        return this.evalRead(newState, edge, array, arrayRef, indexRef);
    }

    /**
     * Actually get the value out of the array.
     * @param indexRef reference to the index
     * @param arrayRef reference to the array
     * @param array the array
     * @param edge the edge provided with the resulting state
     * @param newState the resulting state being constructed
     * @return the new state and the connecting edge
     */
    private Pair<State, EvaluationEdge> evalRead(
        final State newState,
        final EvaluationEdge edge,
        final Array array,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef)
    {
        //Get data and push it onto the stack. Everything else is sorted out by Array.load():
        final AbstractVariableReference result = array.load(newState, arrayRef, indexRef);
        newState.getCurrentStackFrame().getOperandStack().pop();
        newState.getCurrentStackFrame().getOperandStack().pop();

        newState.getCurrentStackFrame().pushOperandStack(result);

        if (array instanceof AbstractArray) {
            edge.add(new AbstractArrayAccessInformation(this.readWriteType, arrayRef, result, indexRef));
        } else {
            edge.add(new ArrayAccessInformation(this.readWriteType, arrayRef, result, indexRef));
        }
        return new Pair<>(newState, edge);
    }

    /**
     * Do the type check and actually write to the array.
     * @param splitRes the split result
     * @param indexRef reference to the index
     * @param arrayRef reference to the array
     * @param array the array
     * @param edge the edge provided with the resulting state
     * @param newState the resulting state being constructed
     * @param valueRef reference to the value written into the array
     * @return the new state and the connecting edge
     */
    private Pair<State, EvaluationEdge> evalWrite(
        final ArrayAccessSplitResult splitRes,
        final State newState,
        final EvaluationEdge edge,
        final Array array,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef,
        final AbstractVariableReference valueRef)
    {
        assert (valueRef != null);
        AbstractVariableReference newValueRef = valueRef;
        Boolean isStorable = null;
        if (splitRes != null) {
            isStorable = splitRes.needsArrayStoreException();
        }

        // we do not have a type check for primitives, values are truncated
        if (this.operandType.isPrimitive()) {
            isStorable = Boolean.TRUE;
        } else if (isStorable == null) {
            //Check if the values are compatible:
            final AbstractType valueType = newState.getAbstractType(newValueRef);
            final AbstractType arrayType = newState.getAbstractType(arrayRef);

            //Check if we need to refine here. First construct the value type:
            //The primitive case:
            if (newValueRef.isNULLRef()) {
                //If the value is the null pointer, it is always correctly typed:
                isStorable = Boolean.TRUE;
            } else {
                if (valueType == null) {
                    isStorable = false;
                } else {
                    //Last stop before actually storing: Check if the types are compatible:
                    isStorable = valueType.isStorageCompatibleTo(arrayType, newState.getClassPath(), newState.getJBCOptions());
                }
                assert (isStorable != null) : "Refinement/Split failed, some value types aren't assignable to some array types";

            }
        }

        if (!isStorable.booleanValue()) {
            /*
             * No need to init (which we cannot do in evaluate(), anyways), see
             * State.demandInitialization()
             */
            OpCode.throwException(newState, ARRAYSTORE_EXC);
            return new Pair<>(newState, edge);
        }

        //Wow, everything is fine, so actually do the write:
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach =
            array.store(newState, arrayRef, indexRef, newValueRef, this.operandType.isPrimitive());

        if (array instanceof AbstractArray) {
            edge.add(new AbstractArrayAccessInformation(this.readWriteType, arrayRef, newValueRef, indexRef));
        } else {
            edge.add(new ArrayAccessInformation(this.readWriteType, arrayRef, newValueRef, indexRef));
        }

        newState.getCurrentStackFrame().getOperandStack().pop();
        newState.getCurrentStackFrame().getOperandStack().pop();
        newState.getCurrentStackFrame().getOperandStack().pop();
        newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());

        edge.addAll(newDefReach);

        return new Pair<>(newState, edge);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        if (this.readWriteType == FieldAccessRW.READ) {
            return "Read " + this.operandType + " from array";
        }
        return "Write " + this.operandType + " to array";
    }

    /** {@inheritDoc} */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame preEvalFrame = preEval.getCurrentStackFrame();
        final StackFrame preEvalInstFrame = preEvalInst.getCurrentStackFrame();

        if (this.readWriteType == FieldAccessRW.READ) {
            final AbstractVariableReference readValRef = preEvalInstFrame.getOperandStack().pop();

            /*
             * We really want to only consider concrete array accesses, so
             * ensure that the value is a literal by setting it to one:
             */
            final AbstractVariableReference abstrIndexRef = preEvalFrame.getOperandStack().peek(0);
            final AbstractVariableReference concrIndexRef;
            if (refMap.containsKey(abstrIndexRef)) {
                concrIndexRef = refMap.get(abstrIndexRef);
            } else if (abstrIndexRef.pointsToConstantInt()) {
                concrIndexRef = abstrIndexRef;
                //Ensure that the value is around:
                final AbstractVariable val = preEvalInst.getAbstractVariable(concrIndexRef);
                if (val == null) {
                    preEvalInst.addAbstractVariable(concrIndexRef, preEval.getAbstractVariable(abstrIndexRef));
                }
            } else {
                concrIndexRef = null;
            }
            assert (concrIndexRef != null) : "Could not identify accessed index";

            AbstractInt concrIndex = (AbstractInt) preEvalInst.getAbstractVariable(concrIndexRef);

            if (!(concrIndex instanceof LiteralInt)) {
                final BigInteger lowerIndexBoundBI = (concrIndex).getLower().getConstant();
                assert (lowerIndexBoundBI != null) : "Illegal array access with -inf index!";
                concrIndex = AbstractInt.create(lowerIndexBoundBI.intValue());
                preEvalInst.removeAbstractVariable(concrIndexRef);
                preEvalInst.addAbstractVariable(concrIndexRef, concrIndex);
            }

            final int index = ((LiteralInt) concrIndex).getLiteral().intValue();

            /*
             * Again, we only want to consider concrete array accesses,
             * so ensure that the array is in fact a concrete one:
             */
            final AbstractVariableReference abstrArrayRef = preEvalFrame.getOperandStack().peek(1);
            final AbstractVariableReference concrArrayRef = refMap.get(abstrArrayRef);
            assert (concrArrayRef != null) : "Could not identify accessed array";

            Array concrArray = (Array) preEvalInst.getAbstractVariable(concrArrayRef);
            if (!(concrArray instanceof ConcreteArray)) {
                final AbstractVariableReference concrArrayLengthRef = concrArray.getLength();
                AbstractInt concrArrayLength = (AbstractInt) preEvalInst.getAbstractVariable(concrArrayLengthRef);

                if (!(concrArrayLength instanceof LiteralInt)) {
                    final BigInteger lowerLengthBoundBI = (concrArrayLength).getLower().getConstant();
                    assert (lowerLengthBoundBI != null) : "Illegal array length with -inf!";
                    final int newLength = Math.max(index + 1, lowerLengthBoundBI.intValue());
                    concrArrayLength = AbstractInt.create(newLength);
                    preEvalInst.removeAbstractVariable(concrArrayLengthRef);
                    preEvalInst.addAbstractVariable(concrArrayLengthRef, concrArrayLength);
                }

                //We now have a length, create the concrete array:
                final AbstractType abstrArrayType = preEvalInst.getAbstractType(concrArrayRef);
                assert (abstrArrayType.getPossibleClassesCopy().size() == 1);
                concrArray =
                    new ConcreteArray(concrArrayLengthRef, preEvalInst, abstrArrayType
                        .getPossibleClassesCopy()
                        .iterator()
                        .next()
                        .getEnclosedType());
                preEvalInst.removeAbstractVariable(concrArrayRef);
                preEvalInst.addAbstractVariable(concrArrayRef, concrArray);
            }

            // Now put the read value into the right place:
            ((ConcreteArray) concrArray).put(index, readValRef);

            // Last step: Put in the refs to array and index:
            preEvalInstFrame.getOperandStack().push(concrArrayRef);
            preEvalInstFrame.getOperandStack().push(concrIndexRef);
            preEvalInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

            return preEvalInst;
        } else {
            throw new NotYetImplementedException();
        }
    }

    @Override
    public int getNumberOfArguments() {
        switch(readWriteType) {
            case READ: return 2;
            case WRITE: return 3;
            default: throw new RuntimeException();
        }
    }

    @Override
    public int getNumberOfOutputs() {
        switch(readWriteType) {
            case READ: return 1;
            case WRITE: return 0;
            default: throw new RuntimeException();
        }
    }

}
