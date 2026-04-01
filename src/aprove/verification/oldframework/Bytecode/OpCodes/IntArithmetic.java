/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of arithmetic operations on abstract integer variables.
 */
public class IntArithmetic extends OpCode {
    /**
     * Type of arithmetic operation represented by this instance.
     */
    private final ArithmeticOperationType operationType;

    /**
     * Type of the result of this operation (and hence, also the operands)
     */
    private final IntegerType resultType;

    /**
     * Construct a new instance representing the documented operation.
     * @param opType type of arithmetic operation
     * @param resType type of the result of this operation (and hence, also the operands)
     */
    public IntArithmetic(final ArithmeticOperationType opType, final IntegerType resType) {
        this.operationType = opType;
        this.resultType = resType;
    }

    /**
     * Refinement to get states in which <code>intRef</code> points to an
     * {@link AbstractInt} which contains either only 0 or no 0. This also
     * initializes ArithmeticException, if needed.
     * @param curState state to work on
     * @param intRef reference to an integer which should be refined into 0 (the
     * literal) and != 0.
     * @param newStates list to push result state/edges in
     * @return true iff a refinement was possible.
     */
    private static boolean forZero(
        final State curState,
        final AbstractVariableReference intRef,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {

        // Get the value:
        final AbstractInt abstrInt = (AbstractInt) curState.getAbstractVariable(intRef);

        // Easy ways out:
        if (!abstrInt.containsLiteral(0)) {
            return false;
        }

        if (abstrInt.isLiteral()) {
            return ObjectRefinement.forInitialization(Important.ARITH_EXC, curState, newStates);
        }

        // OK, get a state containing zero:
        final State zeroState = curState.clone();
        final AbstractInt zero = AbstractInt.getZero();
        final AbstractVariableReference newRef = zeroState.createReferenceAndAdd(zero, intRef.getPrimitiveType());
        zeroState.replaceReference(intRef, newRef);
        final RefinementEdge edge = new RefinementEdge(intRef, newRef);
        edge.add(new JBCIntegerRelation(newRef, IntegerRelationType.EQ, 0));
        newStates.add(new Pair<State, EdgeInformation>(zeroState, edge));

        // Now do the non-zero state:
        final State notZeroState = curState.clone();
        final AbstractInt notZero = abstrInt.removeZeroFromInteger();
        final AbstractVariableReference newRefNotZero =
            notZeroState.createReferenceAndAdd(notZero, intRef.getPrimitiveType());
        notZeroState.replaceReference(intRef, newRefNotZero);
        final RefinementEdge edgeNotZero = new RefinementEdge(intRef, newRefNotZero);
        edge.add(new JBCIntegerRelation(newRefNotZero, IntegerRelationType.NE, 0));
        newStates.add(new Pair<State, EdgeInformation>(notZeroState, edgeNotZero));

        return true;
    }

    /** {@inheritDoc} */
    @Override
    public final Pair<State, ? extends EdgeInformation> evaluate(final State state) {
        final State newState = state.clone();

        //Get data:
        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference opBR = curFrame.popOperandStack();
        assert (newState.getAbstractVariable(opBR) instanceof AbstractInt);
        final AbstractInt opB = (AbstractInt) newState.getAbstractVariable(opBR);

        AbstractVariableReference opAR = null;
        AbstractInt opA = null;
        final boolean sameReference;
        AbstractInt res = null;

        final OperandType opTypeOfRes =
            (this.resultType == IntegerType.JAVA_INT) ? OperandType.INTEGER : OperandType.LONG;

        final AbstractVariableReference resR;
        boolean throwArithmeticException = false;
        boolean contradictory = false;
        if (this.operationType == ArithmeticOperationType.NEG) {
            //NEG only needs one value
            res = opB.negate(this.resultType);
            if (res.isZero()) {
                resR = opBR;
            } else {
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
            }
        } else {
            opAR = curFrame.popOperandStack();
            assert (newState.getAbstractVariable(opAR) instanceof AbstractInt);
            opA = (AbstractInt) newState.getAbstractVariable(opAR);
            sameReference = opAR.equals(opBR);
            Pair<? extends AbstractInt, Boolean> pair;
            Triple<? extends AbstractInt, Boolean, Boolean> triple;
            switch (this.operationType) {
            case ADD:
                res = opA.add(opB, this.resultType);
                if (opA.isZero()) {
                    resR = opBR;
                } else if (opB.isZero()) {
                    resR = opAR;
                } else {
                    resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                }
                if (opB.isLiteral()) {
                    final int opBLit = opB.getLiteral().intValue();
                    contradictory |= newState.noteNewRefInRelation(resR, opAR, opBLit);
                    if (opBLit > 0) {
                        contradictory |= newState.note(resR, IntegerRelationType.GT, opAR);
                    } else if (opBLit < 0) {
                        contradictory |= newState.note(resR, IntegerRelationType.LT, opAR);
                    }
                }
                if (opA.isLiteral()) {
                    final int opALit = opA.getLiteral().intValue();
                    contradictory |= newState.noteNewRefInRelation(resR, opBR, opALit);
                    if (opALit > 0) {
                        contradictory |= newState.note(resR, IntegerRelationType.GT, opBR);
                    } else if (opALit < 0) {
                        contradictory |= newState.note(resR, IntegerRelationType.LT, opBR);
                    }
                }
                break;
            case AND:
                res = opA.and(opB, sameReference, this.resultType);
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                break;
            case TIDIV:
                triple = opA.div(opB, sameReference, this.resultType);
                res = triple.x;
                throwArithmeticException = triple.y.booleanValue();
                assert (!throwArithmeticException || res == null);
                if (res != null) {
                    if (opB.isOne()) {
                        resR = opAR;
                    } else {
                        resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                    }
                } else {
                    resR = null;
                }
                break;
            case MUL:
                res = opA.mul(opB, this.resultType);
                if (opB.isOne()) {
                    resR = opAR;
                } else {
                    resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                }
                break;
            case OR:
                res = opA.or(opB, sameReference, this.resultType);
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                break;
            case TMOD:
                pair = opA.rem(opB, sameReference, this.resultType);
                res = pair.x;
                throwArithmeticException = pair.y.booleanValue();
                assert (!throwArithmeticException || res == null);
                if (res != null) {
                    resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                } else {
                    resR = null;
                }
                break;
            case SHL:
                res = opA.shl(opB, this.resultType);
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                break;
            case SHR:
                res = opA.shr(opB, this.resultType);
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                break;
            case SUB:
                boolean subtrahendSmaller = false;
                boolean subtrahendSmallerOrEqual = false;
                if (state.getIntegerRelations().contains(new JBCIntegerRelation(opAR, IntegerRelationType.GT, opBR))) {
                    if (state.checkIntegerRelation(new JBCIntegerRelation(opAR, IntegerRelationType.LE, opBR))) {
                        // this state is contradictory - abort evaluation
                        return null;
                    }
                    subtrahendSmaller = true;
                    subtrahendSmallerOrEqual = true;
                } else if (state
                    .getIntegerRelations()
                    .contains(new JBCIntegerRelation(opAR, IntegerRelationType.GE, opBR)))
                {
                    if (state.checkIntegerRelation(new JBCIntegerRelation(opAR, IntegerRelationType.LT, opBR))) {
                        // this state is contradictory - abort evaluation
                        return null;
                    }
                    subtrahendSmallerOrEqual = true;
                }
                res = opA.sub(opB, sameReference, subtrahendSmaller, subtrahendSmallerOrEqual, this.resultType);
                if (opB.isZero()) {
                    resR = opAR;
                } else {
                    resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                }
                if (opB.isLiteral()) {
                    final int opBLit = opB.getLiteral().intValue();
                    contradictory |= newState.noteNewRefInRelation(resR, opAR, -opBLit);
                    if (opBLit > 0) {
                        contradictory |= newState.note(resR, IntegerRelationType.LT, opAR);
                    } else if (opBLit < 0) {
                        contradictory |= newState.note(resR, IntegerRelationType.GT, opAR);
                    }
                }
                break;
            case USHR:
                res = opA.ushr(opB, this.resultType);
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                break;
            case XOR:
                res = opA.xor(opB, sameReference, this.resultType);
                resR = newState.createReferenceAndAdd(res, opTypeOfRes);
                break;
            default:
                resR = null;
                assert (false) : "Unknown arithmetic/bitwise operation on ints";
            }
        }

        if (throwArithmeticException) {
            final State clone = state.clone();
            OpCode.throwException(clone, ARITH_EXC);
            return new Pair<>(clone, new MethodStartEdge());
        }

        assert (res != null) : "There has to be a result for an arithmetic expression";

        curFrame.pushOperandStack(resR);

        curFrame.setCurrentOpCode(this.getNextOp());

        final EvaluationEdge info = new EvaluationEdge();

        if (opA == null || !(opA.isLiteral() && opB.isLiteral())) {
            /*
             * Encoding shifts is difficult, since there is no support in the
             * ITSR framework and only the lower 5 or 6 bits of the operand are
             * regarded.
             */
            if (opA != null && this.operationType == ArithmeticOperationType.SHL) {
                if (res.getLower().isFinite() && res.getUpper().isFinite() && opB.isLiteral()) {
                    // we just did res = opA * 2^opB
                    int lowBits = opB.getLiteral().intValue();
                    if (opAR.pointsToLong()) {
                        lowBits = lowBits & 0x3f;
                    } else {
                        lowBits = lowBits & 0x1f;
                    }
                    final LiteralInt twos = AbstractInt.create(1 << lowBits);
                    info.add(new IntegerResultInformation(opAR, ArithmeticOperationType.MUL, twos, resR));
                }
            } else if (this.operationType != ArithmeticOperationType.SHR && this.operationType != ArithmeticOperationType.USHR) {
                info.add(new IntegerResultInformation(opAR, this.operationType, opBR, resR));
            }
        }
        assert !contradictory;
        return new Pair<>(newState, info);
    }

    /** {@inheritDoc} */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        /*
         * We only need to refine if the operation is a division or modulo, and the second
         * operator is zero
         */
        switch (this.operationType) {
            case MDIV:
            case FDIV:
            case EIDIV:
            case TIDIV:
            case FIDIV:
            case EMOD:
            case TMOD:
            case FMOD:
                // Get the reference to the divisor:
                final AbstractVariableReference divisorRef = s.getCurrentStackFrame().getOperandStack().peek(0);
                return IntArithmetic.forZero(s, divisorRef, out);
            default:
                return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curAbstrFrame = preEval.getCurrentStackFrame();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();
        curInstFrame.setCurrentOpCode(curAbstrFrame.getCurrentOpCode());

        //Get rid of result:
        final AbstractVariableReference resRef = curInstFrame.popOperandStack();
        final AbstractInt resVal = (AbstractInt) postEvalInst.getAbstractVariable(resRef);

        //Just copy in the abstract values:
        AbstractVariableReference operandTwoRef =
            State.mapOrCopyRef(preEval, preEvalInst, curAbstrFrame.peekOperandStack(0), refMap);

        AbstractInt operandTwoVal = (AbstractInt) preEvalInst.getAbstractVariable(operandTwoRef);

        if (this.operationType == ArithmeticOperationType.NEG) {
            if (resVal instanceof LiteralInt) {
                operandTwoVal = ((LiteralInt) resVal).negate(IntegerType.UNBOUND);
                operandTwoRef = preEvalInst.createReferenceAndAdd(operandTwoVal, operandTwoRef.getPrimitiveType());
            }

            //If this is not NEG, we have two operands:
        } else {
            AbstractVariableReference operandOneRef =
                State.mapOrCopyRef(preEval, preEvalInst, curAbstrFrame.peekOperandStack(1), refMap);
            AbstractInt operandOneVal = (AbstractInt) preEvalInst.getAbstractVariable(operandOneRef);

            if (this.operationType == ArithmeticOperationType.TMOD
                && operandOneVal instanceof IntervalInt
                && operandTwoVal instanceof LiteralInt
                && resVal instanceof LiteralInt)
            {
                final long divisor = ((LiteralInt) operandTwoVal).getLongValue();
                final long res = ((LiteralInt) resVal).getLongValue();
                //Find just one element of the range represented by the first
                final IntervalInt operandOneInterval = (IntervalInt) operandOneVal;
                final IntervalBound opOneLowBound = operandOneInterval.getLower();

                final IntervalBound opOneUpBound = operandOneInterval.getUpper();
                final long lowBound;
                final long upBound;
                if (!opOneLowBound.isFinite()) {
                    if (opOneUpBound.isFinite()) {
                        upBound = opOneUpBound.getConstant().longValue();
                        lowBound = upBound - divisor;
                    } else {
                        lowBound = 0;
                        upBound = divisor;
                    }
                } else {
                    lowBound = opOneLowBound.getConstant().longValue();
                    if (opOneUpBound.isFinite()) {
                        upBound = opOneUpBound.getConstant().longValue();
                    } else {
                        upBound = lowBound + divisor;
                    }
                }

                long firstOpVal = lowBound / divisor * divisor;
                if (res != 0 || firstOpVal < lowBound) {
                    firstOpVal += res;
                }
                if (firstOpVal < lowBound) {
                    firstOpVal += divisor;
                }
                final boolean foundVal = firstOpVal <= upBound;

                assert (foundVal) : "Arithmetic broken, can't find fitting result!";
                operandOneVal = AbstractInt.create(firstOpVal);
                final AbstractVariableReference newOperandOneRef =
                    preEvalInst.createReferenceAndAdd(operandOneVal, operandOneRef.getPrimitiveType());
                preEvalInst.replaceReference(operandOneRef, newOperandOneRef);
                operandOneRef = newOperandOneRef;
            } else if (this.operationType == ArithmeticOperationType.MUL
                && resVal instanceof LiteralInt
                && (operandOneVal instanceof LiteralInt || operandTwoVal instanceof LiteralInt))
            {
                //Multiplication can be reversed if we have literal. Muhahahaha.
                if (operandOneVal instanceof LiteralInt) {
                    operandTwoVal = resVal.div(operandOneVal, false, IntegerType.UNBOUND).x;
                    final AbstractVariableReference newOperandTwoRef =
                        preEvalInst.createReferenceAndAdd(operandTwoVal, operandTwoRef.getPrimitiveType());
                    preEvalInst.replaceReference(operandTwoRef, newOperandTwoRef);
                    operandTwoRef = newOperandTwoRef;
                } else if (operandTwoVal instanceof LiteralInt) {
                    operandOneVal = resVal.div(operandTwoVal, false, IntegerType.UNBOUND).x;
                    final AbstractVariableReference newOperandOneRef =
                        preEvalInst.createReferenceAndAdd(operandOneVal, operandOneRef.getPrimitiveType());
                    preEvalInst.replaceReference(operandOneRef, newOperandOneRef);
                    operandOneRef = newOperandOneRef;
                }

                /*
                 * Try some easy guesses: If one of the variables was already
                 * widened, it's probably used in the loop.
                 */
            } else if (!operandOneVal.isLiteral() && !operandTwoVal.isLiteral()) {
                final IntervalInt intervalOne = (IntervalInt) operandOneVal;
                final IntervalInt intervalTwo = (IntervalInt) operandTwoVal;

                AbstractVariableReference usedInLoop = null;
                AbstractVariableReference unusedInLoop = null;
                if (intervalOne.wasWidened()) {
                    usedInLoop = operandOneRef;
                } else {
                    unusedInLoop = operandOneRef;
                }
                if (intervalTwo.wasWidened()) {
                    usedInLoop = operandTwoRef;
                } else {
                    unusedInLoop = operandTwoRef;
                }

                if (usedInLoop != null && unusedInLoop != null) {
                    //Try using the absolute minimum for the unused value:
                    final IntervalInt unusedVal = (IntervalInt) preEvalInst.getAbstractVariable(unusedInLoop);
                    final IntervalBound upperBound = unusedVal.getUpper();
                    final IntervalBound lowerBound = unusedVal.getLower();

                    final long newValue;
                    if (lowerBound.isFinite() && upperBound.isFinite()) {
                        if (lowerBound.compareTo(upperBound.abs()) <= 0) {
                            newValue = lowerBound.getConstant().longValue();
                        } else {
                            newValue = upperBound.getConstant().longValue();
                        }
                    } else if (lowerBound.isFinite()) {
                        newValue = lowerBound.getConstant().longValue();
                    } else if (upperBound.isFinite()) {
                        newValue = upperBound.getConstant().longValue();
                    } else {
                        newValue = 0;
                    }

                    final LiteralInt newLiteralInt = AbstractInt.create(newValue);

                    final AbstractVariableReference newLiteralIntRef =
                        preEvalInst.createReferenceAndAdd(newLiteralInt, operandOneRef.getPrimitiveType());
                    if (operandOneRef == unusedInLoop) {
                        operandOneRef = newLiteralIntRef;
                    } else {
                        operandTwoRef = newLiteralIntRef;
                    }
                }
            }

            curInstFrame.pushOperandStack(operandOneRef);
        }
        curInstFrame.pushOperandStack(operandTwoRef);

        return preEvalInst;
    }

    /** {@inheritDoc} */
    @Override
    public final String toString() {
        return this.operationType.toLongString();
    }

    @Override
    public int getNumberOfArguments() {
        switch (operationType) {
            case NEG: return 1;
            default: return 2;
        }
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
