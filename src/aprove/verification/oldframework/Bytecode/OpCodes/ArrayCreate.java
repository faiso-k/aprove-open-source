package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of the newarray, multianewarray and anewarray opcodes.
 * @author Marc Brockschmidt
 */
public class ArrayCreate extends OpCode {
    /**
     * Full type of the array contents, including the array depths and inner
     * type.
     */
    private final FuzzyType arrayType;

    /**
     * Number of count arguments to be popped from the operand stack when
     * creating the array.
     */
    private final int numberOfLengthArgs;

    /**
     * Iff true, this opcode represents multianewarray.
     */
    private final boolean isMulti;

    /**
     * Create a new "newarray", "anewarray" or "multianewarray" opcode.
     * @param type Type of the array.
     * @param dimensions number of size args to be popped from the stack
     * @param isMultiParam iff true, this opcode represents multianewarray.
     */
    public ArrayCreate(final FuzzyType type, final int dimensions, final boolean isMultiParam) {
        assert (type.isArrayType()) : "Trying to create an array of a non-array type";
        this.arrayType = type;
        this.numberOfLengthArgs = dimensions;
        this.isMulti = isMultiParam;
    }

    /**
     * @return a nice string representation of this opcode
     */
    @Override
    public String toString() {
        if (this.isMulti) {
            return "multianewarray " + this.arrayType + " (dimensions: " + this.numberOfLengthArgs + ")";
        }
        if (this.arrayType.getEnclosedType() instanceof FuzzyPrimitiveType) {
            return "newarray " + this.arrayType;
        }
        return "anewarray " + this.arrayType;
    }

    /**
     * Check if we need to throw a NegativeArraySizeException.
     * @param state Input state
     * @param result Object used for collecting the result
     * @return true if refinement was needed and done, false if no refinement
     * was needed
     */
    @Override
    public boolean refine(final State state, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        /*
         * Check that for all lengths given on the operand stack we know if the
         * length is negative or not (to decide if a NegativeArraySizeException
         * needs to be thrown). If the array length is a non-int constant, we have a failed refinement.
         */
        final StackFrame frame = state.getCurrentStackFrame();
        for (int i = this.numberOfLengthArgs - 1; i >= 0; i--) {
            final AbstractVariableReference arrayLength = frame.peekOperandStack(i);
            assert (arrayLength.pointsToInteger());

            final AbstractInt aInt = (AbstractInt) state.getAbstractVariable(arrayLength);

            if (aInt.isLiteral()) {
                if (aInt.getLiteral().compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
                    result.add(new Pair<>(state.clone(), new FailedRefinementEdge("array length too big")));
                    return true;
                }
            }

            // >= 0: Everything is good.
            if (aInt.isNonNegative()) {
                continue;
            }

            // < 0: Bad.
            if (aInt.isNegative()) {
                if (ObjectRefinement.forInitialization(Important.NEGARRAYSIZE_EXC, state, result)) {
                    return true;
                }
                continue;
            }

            // We have no clue, refine!
            final State stateNegative = state.clone();
            final AbstractInt varNegative = aInt.onlyNegative();
            final AbstractVariableReference refNegative =
                stateNegative.createReferenceAndAdd(varNegative, OperandType.INTEGER);
            stateNegative.replaceReference(arrayLength, refNegative);

            final State stateNonNegative = state.clone();
            final AbstractInt varNonNegative = aInt.onlyNonNegative();
            final AbstractVariableReference refNonNegative =
                stateNonNegative.createReferenceAndAdd(varNonNegative, OperandType.INTEGER);
            stateNonNegative.replaceReference(arrayLength, refNonNegative);

            result.add(new Pair<State, EdgeInformation>(stateNegative, new RefinementEdge(arrayLength, refNegative)));
            result.add(new Pair<State, EdgeInformation>(stateNonNegative, new RefinementEdge(
                arrayLength,
                refNonNegative)));
            return true;
        }
        return false;
    }

    /**
     * Generates exactly one new state from the current state by creating a new
     * array of the specified type and length from the operand stack. In case of
     * multianewarray this array in turn is filled with arrays of another given
     * length etc.
     * @param state The old state
     * @return the successor state created by this operation.
     */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State state) {
        final State newState = state.clone();

        final StackFrame frame = newState.getCurrentStackFrame();
        /*
         * The negative array size exception is only thrown for (a)newarray,
         * it's not needed for multinewarray:
         */
        if (!this.isMulti) {
            final AbstractInt arrayLength = (AbstractInt) state.getAbstractVariable(frame.peekOperandStack(0));
            if (arrayLength.isNegative()) {
                /*
                 * The index is negative. So, we need to throw a
                 * NegativeArraySizeException.
                 */
                OpCode.throwException(newState, NEGARRAYSIZE_EXC);
                return new Pair<>(newState, new MethodStartEdge());
            }
        }

        /*
         * OK, actual array creation. At the end, we just want the ref to
         * the outermost array
         */
        AbstractVariableReference newOutermostArrayRef = null;
        List<AbstractVariableReference> parentArrays = new LinkedList<>();
        FuzzyType currentlyRealizedType = this.arrayType;
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach = new LinkedHashSet<>();
        for (int realizedDepth = this.numberOfLengthArgs - 1; realizedDepth >= 0; realizedDepth--) {
            final AbstractVariableReference arrayLengthRef = frame.peekOperandStack(realizedDepth);

            //First dimension:
            if (newOutermostArrayRef == null) {
                newOutermostArrayRef =
                    ArrayCreate.createAndAddArray(newState, currentlyRealizedType, arrayLengthRef, this.numberOfLengthArgs <= 1);
                parentArrays.add(newOutermostArrayRef);

                /* This is the nth, n > 2, dimension:
                 *  (1) Iterate through the list of all arrays created
                 *      in the last dim
                 *    (2) Get the length for arrays in the last dimension
                 *    (3) For each of the fields of the old arrays,
                 *        create a new one.
                 *    (4) Store it for the next dimension.
                 */
            } else {
                final List<AbstractVariableReference> newParentArrays = new LinkedList<>();
                for (final AbstractVariableReference parentArrayRef : parentArrays) {
                    final Array parentArray = (Array) newState.getAbstractVariable(parentArrayRef);

                    /*
                     * If we have a literal length of the parent array, write into each cell. Otherwise, just do a
                     * single abstract write.
                     */
                    final LinkedList<AbstractVariableReference> indexRefs = new LinkedList<>();
                    final AbstractVariableReference parentArrayLengthRef = parentArray.getLength();
                    if (parentArrayLengthRef.pointsToConstantInt()) {
                        final int parentArrayLength =
                            ((AbstractInt) newState.getAbstractVariable(parentArrayLengthRef)).getLiteral().intValue();
                        for (int i = parentArrayLength - 1; i >= 0; i--) {
                            final AbstractVariableReference indexRef =
                                newState.createReferenceAndAdd(AbstractInt.create(i), OperandType.INTEGER);
                            indexRefs.addFirst(indexRef);
                            newState.getCurrentStackFrame().pushOperandStack(indexRef);
                        }
                    } else {
                        final AbstractVariableReference indexRef =
                                newState.createReferenceAndAdd(
                                        AbstractInt.create(IntervalBound.ZERO,
                                                IntegerType.UNBOUND.getUpper(),
                                                IntervalBound.ZERO,
                                                IntegerType.UNBOUND.getUpper(),
                                                0,
                                                0),
                                        OperandType.INTEGER);
                        indexRefs.add(indexRef);
                    }

                    for (final AbstractVariableReference indexRef : indexRefs) {
                        final AbstractVariableReference newArrayRef =
                            ArrayCreate.createAndAddArray(newState, currentlyRealizedType, arrayLengthRef, false);

                        if (parentArray instanceof ConcreteArray) {
                            assert (indexRef.pointsToConstantInt());
                            final AbstractInt aInt = (AbstractInt) newState.getAbstractVariable(indexRef);
                            ((ConcreteArray) parentArray).put(aInt.getLiteral().intValue(), newArrayRef);
                        } else {
                            // push reference of outermost array, but do not gc() that
                            newState.getCurrentStackFrame().pushOperandStack(newOutermostArrayRef);

                            // push references for parent array and current array, these may be gc()ed
                            newState.getCurrentStackFrame().pushOperandStack(parentArrayRef);
                            newState.getCurrentStackFrame().pushOperandStack(newArrayRef);
                            newDefReach.addAll(parentArray
                                .store(newState, parentArrayRef, indexRef, newArrayRef, false));
                            newState.getCurrentStackFrame().popOperandStack();
                            newState.getCurrentStackFrame().popOperandStack();
                            newState.gc();

                            // remove reference for outermost array again
                            newState.getCurrentStackFrame().popOperandStack();

                            if (indexRef.pointsToConstantInt()) {
                                // we pushed these constant ints, remove them now
                                newState.getCurrentStackFrame().popOperandStack();
                            }
                        }

                        newParentArrays.add(newArrayRef);
                    }
                }
                parentArrays = newParentArrays;
            }

            /*
             * Now remember, kids, enclosed arrays shouldn't have the same type
             * as the enclosing array:
             */
            currentlyRealizedType = currentlyRealizedType.getEnclosedType();
        }

        // now drop the length information
        for (int i = 0; i < this.numberOfLengthArgs; i++) {
            frame.popOperandStack();
        }

        frame.pushOperandStack(newOutermostArrayRef);
        frame.setCurrentOpCode(this.getNextOp());
        final EvaluationEdge edge = new EvaluationEdge();
        edge.addAll(newDefReach);
        return new Pair<>(newState, edge);
    }

    /**
     * Create a new @link {@link Array}-implementing variable and prepare the
     * state with type and other information.
     * @param state state in which this array is used (needed for variable
     * lookups)
     * @param type type of the array to create
     * @param arrayLengthRef reference to the length of this array
     * @param allowConcrete if false, only abstract arrays will be created
     * @return an {@link AbstractVariableReference} pointing to the newly
     * created array.
     */
    private static AbstractVariableReference createAndAddArray(
        final State state,
        final FuzzyType type,
        final AbstractVariableReference arrayLengthRef,
        final boolean allowConcrete)
    {
        final AbstractVariableReference res;

        final AbstractInt arrayLength = (AbstractInt) state.getAbstractVariable(arrayLengthRef);

        final Array resArr;
        if (arrayLength.isLiteral() && allowConcrete && arrayLength.getLiteral().longValue() <= 127) {
            resArr = new ConcreteArray(arrayLengthRef, state, type.getEnclosedType());
        } else {
            resArr = new AbstractArray(arrayLengthRef);
        }

        res = state.createReferenceAndAdd(resArr, OperandType.ARRAY);
        state.getHeapAnnotations().setAbstractType(
            res,
            new AbstractType(state.getClassPath(), state.getJBCOptions(), Collections.singleton(type)));
        state.getHeapAnnotations().setReachableTypes(
            res,
            new AbstractType(state.getClassPath(), FuzzyClassType.FT_JAVA_LANG_OBJECT));
        return res;
    }

    @Override
    public State reverseEvaluation(State preEval, State postEval, State postEvalInst,
            Map<AbstractVariableReference, AbstractVariableReference> refMap) {
        final State preEvalInst = postEvalInst.clone();

        //pop result
        preEvalInst.getCurrentStackFrame().popOperandStack();
        //get length args
        final LinkedList<AbstractVariableReference> poppedRefs = new LinkedList<>();
        for (int i = 0; i < this.numberOfLengthArgs; i++) {
            poppedRefs.add(preEval.getCurrentStackFrame().getOperandStack().peek(i));
        }
        //push length args
        final Iterator<AbstractVariableReference> it = poppedRefs.descendingIterator();
        while (it.hasNext()) {
            preEvalInst
                .getCurrentStackFrame()
                .getOperandStack()
                .push(State.mapOrCopyRef(preEval, preEvalInst, it.next(), refMap));
        }
        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return numberOfLengthArgs;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
