package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Push constant data from constant pool to operand stack.
 * @author Christian von Essen
 */
public class ConstantStackPush extends OpCode {
    /** Enumeration of all the different things we can push onto the operand stack */
    public enum StackPushType {
        /** Push a string value */
        STRING,
        /** Push a 32 bit integer number */
        INTEGER,
        /** Push a 64 bit integer number */
        LONG,
        /** Push a 32 bit floating point number */
        FLOAT,
        /** Push a 64 bit floating point number */
        DOUBLE,
        /** Push an instance of class java/lang/Class */
        CLASS,
        /** Push the NULL pointer */
        NULL;
    }

    /**
     * Some object holding the value to push to the stack.
     */
    private final Object constantToPush;

    /**
     * Type of the constant value to push.
     */
    private final StackPushType typeToPush;

    /**
     * Create a new stack push instance, pushing some constant to the operand
     * stack.
     * @param constToPush the object holding the value to push (should match
     *  the information in pushedConstantType)
     * @param pushedConstantType the type of the object to push
     */
    public ConstantStackPush(final Object constToPush, final StackPushType pushedConstantType) {
        this.constantToPush = constToPush;
        this.typeToPush = pushedConstantType;
    }

    /**
     * @return String representation of this {@link ConstantStackPush} opcode.
     */
    @Override
    public final String toString() {
        String v = "";
        switch (this.typeToPush) {
        case INTEGER:
            v += this.constantToPush.toString();
            break;
        case FLOAT:
            v += this.constantToPush.toString() + "F";
            break;
        case LONG:
            v += this.constantToPush.toString() + "L";
            break;
        case DOUBLE:
            v += this.constantToPush.toString() + "D";
            break;
        case STRING:
            v =
                "\""
                    + this.constantToPush
                        .toString()
                        .substring(0, Math.min(30, this.constantToPush.toString().length())) + "\"";
            break;
        case NULL:
            v = "NULL";
            break;
        case CLASS:
            v += "Class " + this.constantToPush.toString();
            break;
        default:
            assert (false);
        }

        return "push " + v;
    }

    /**
     * For CLASS and STRING push we need to initialize first.
     * @param s Input state
     * @param result the refined states will be added here
     * @return true if refinement was needed and done, false if no refinement
     * was needed
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        switch (this.typeToPush) {
        case CLASS:
            return ObjectRefinement.forInitialization(ClassName.Important.JAVA_LANG_CLASS, s, result);
        case STRING:
            return ObjectRefinement.forInitialization(ClassName.Important.JAVA_LANG_STRING, s, result);
        default:
            return false;
        }
    }

    /**
     * Generates exactly one new state from the current state by pushing the
     * specified constant/type combination onto the stack.
     * @param state The old state
     * @return a list with the one successor state created by evaluating this
     * stack push.
     */
    @Override
    public final Pair<State, ? extends EdgeInformation> evaluate(final State state) {
        final State newState = state.clone();
        //Variable reference which will be pushed onto the stack. The actual
        //value is added to newState in the gigantic switch statement below.
        AbstractVariableReference ref = null;
        //The edge to newState, might be annotated with information about
        //the pushed value.
        final EvaluationEdge info = new EvaluationEdge();

        boolean dontPush = false;

        switch (this.typeToPush) {
        case CLASS:
            ref = JLClassHelper.addConstantClassToStateOrThrow(newState, (FuzzyType) this.constantToPush);
            if (ref == null) {
                dontPush = true;
            }
            break;
        case STRING:
            ref = JLStringHelper.addConstantStringToStateOrThrow(newState, (String) this.constantToPush);
            if (state.getJBCOptions().incorrectlyBoundSizeOfConstantStringsByLength()) {
                info.add(new SizeRelationInformation(ref, IntegerRelationType.LE, SimplePolynomial.create(((String) constantToPush).length())));
            }
            info.add(new SizeRelationInformation(ref, IntegerRelationType.GE, SimplePolynomial.ZERO));
            if (ref == null) {
                dontPush = true;
            }
            break;
        case INTEGER:
            assert (this.constantToPush instanceof Integer) : "Trying to push integer constant, but stored value is "
                + this.constantToPush;
            final LiteralInt abstrInt = AbstractInt.create(((Integer) this.constantToPush).intValue());
            ref = newState.createReferenceAndAdd(abstrInt, OperandType.INTEGER);
            info.add(new ConstantIntegerCreationInformation(ref, abstrInt));
            break;
        case LONG:
            assert (this.constantToPush instanceof Long) : "Trying to push long constant, but stored value is "
                + this.constantToPush;
            final LiteralInt abstrLong = AbstractInt.create(((Long) this.constantToPush).longValue());
            ref = newState.createReferenceAndAdd(abstrLong, OperandType.LONG);
            info.add(new ConstantIntegerCreationInformation(ref, abstrLong));
            break;
        case FLOAT:
            assert (this.constantToPush instanceof Float) : "Trying to push float constant, but stored value is "
                + this.constantToPush;
            final float fValue = ((Float) this.constantToPush).floatValue();
            final AbstractFloat abstrFloat = AbstractFloat.create(fValue);
            ref = newState.createReferenceAndAdd(abstrFloat, OperandType.FLOAT);
            info.add(new ConstantFloatCreationInformation(ref, abstrFloat));
            break;
        case DOUBLE:
            assert (this.constantToPush instanceof Double) : "Trying to push double constant, but stored value is "
                + this.constantToPush;
            final double dValue = ((Double) this.constantToPush).doubleValue();
            final AbstractFloat abstrDouble = AbstractFloat.create(dValue);
            ref = newState.createReferenceAndAdd(abstrDouble, OperandType.DOUBLE);
            info.add(new ConstantFloatCreationInformation(ref, abstrDouble));
            break;
        case NULL:
            assert (this.constantToPush == null) : "Trying to push NULL, but have stored value " + this.constantToPush;
            ref = newState.createReferenceAndAdd(ConcreteInstance.NULL, OperandType.ADDRESS);
            break;
        default:
            assert (false) : "Not implemented constant stack push type " + this.typeToPush;
            return null;
        }
        if (dontPush) {
            return new Pair<>(newState, new MethodStartEdge());
        } else {
            if (Globals.useAssertions) {
                assert (ref != null);
            }
            newState.getCurrentStackFrame().pushOperandStack(ref);
            newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
            return new Pair<>(newState, info);
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

        curInstFrame.popOperandStack();

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return 0;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
