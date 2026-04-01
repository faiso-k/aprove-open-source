package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of the return opcode, used to return from a method. Not to mix up
 * with RET, which returns from a subroutine (and is represented by
 * aprove.verification.oldframework.Bytecode.OpCodes.Ret)
 * @author Marc Brockschmidt
 */
public class Return extends OpCode {
    /**
     * The type of the returned value.
     */
    private final OperandType returnType;

    /**
     * Construct a new instance representing a return call from a method
     * @param retType type of the returned value
     */
    public Return(final OperandType retType) {
        this.returnType = retType;
    }

    @Override
    public String toString() {
        if (this.returnType != null) {
            return "return " + this.returnType;
        }
        return "return"; // return
    }

    /**
     * Drop the top stack frame and put the result on the frame below.
     * @param state the current state that should be evaluated
     * @return the single successor state after evaluation
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        /*
         * As we are now using Method graphs, returning from the last stackframe
         * does not imply termination, but requires us instead to notify the listeners.
         */
        final State clone = state.clone();
        // Pop the top stackframe
        final StackFrame oldFrame = clone.getCallStack().pop();
        //Don't do anything if the callstack is empty
        final StackFrame topSF = clone.getCurrentStackFrame();
        if (topSF != null) {
            final OpCode cOpCode = topSF.getCurrentOpCode();
            //Only do something real if this is neither a return from an exception nor is a class initializer
            if (!topSF.hasException() && !oldFrame.getMethod().isClassInitializer()) {
                // some check and cast
                assert cOpCode instanceof InvokeMethod : "Returning after a non invoke opcode";
                final InvokeMethod invokeMethod = (InvokeMethod) cOpCode;
                // clean the arguments from the opstack and advance the opcode
                invokeMethod.handleReturn(clone);
                if (this.returnType != null) {
                    // get the return value
                    final AbstractVariableReference ref = oldFrame.peekOperandStack(0);
                    if (Globals.useAssertions) {
                        final AbstractVariable av = state.getAbstractVariable(ref);
                        assert (this.returnType.check(av)) : "Type of variable to return and opcode don't match: "
                            + "av="
                            + String.valueOf(av)
                            + ", returnType="
                            + this.returnType
                            + " in State "
                            + state;
                    }
                    // and push it on the new top stackframe
                    topSF.pushOperandStack(ref);

                } // if non void
            } // if normal return
        } // if stackframe exists

        final EvaluationEdge edge;
        // distinguish between class initialization and normal return
        if (oldFrame.getMethod().isClassInitializer()) {
            edge = new CLInitDoneEdge();
            /*
             * Here happens a voodo style method call inside the return
             * instruction. We COULD create a MethodStartEdge here.
             *
             * However, it is also correct to treat this method "inline", i.e,
             * just continue as normal.
             */

            final ClassName cn = oldFrame.getMethod().getClassName();
            // if this is the topmost stack frame, then AProVE was invoked to analyze cinit and we don't care about the current initialization state
            assert (state.getCallStack().getStackFrameList().size() == 1 || clone.getClassInitInfo().getInitializationState(cn, state.getJBCOptions()) == InitStatus.RUNNING);
            clone.getClassInitInfo().setInitialized(cn, InitStatus.YES);

            /*
             * According to thread.cpp in OpenJDK, the method
             * java.lang.System.initializeSystemClass() is called directly after
             * initializing java.lang.Class.
             */
            if (false && oldFrame.getMethod().getClassName().equals(Important.JAVA_LANG_CLASS.getClassName())) {
                final IClass systemClass = state.getClassPath().getClass(Important.JAVA_LANG_SYSTEM);
                final MethodIdentifier id =
                    new MethodIdentifier(
                        Important.JAVA_LANG_SYSTEM.getClassName(),
                        "initializeSystemClass",
                        new ParsedMethodDescriptor("()V"));
                final IMethod method = systemClass.getLocalMethod(id);
                InvokeMethod.addNewStackFrame(clone, method, true, false);
            }
        } else {
            // normal return
            edge = new EvaluationEdge();
        }

        /*
         * If the new state has an empty call stack, then the method has just been left.
         * In other words, the previous state is a method end state.
         * Therefore the graph needs to be notified.
         * We detect the returned empty stackframe in the state.
         */

        return new Pair<>(clone, edge);
    }

    /**
     * @return the return type of this return statement (null for void).
     */
    public OperandType getReturnType() {
        return this.returnType;
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

        final CallStack preEvalCallStack = preEval.getCallStack();

        final StackFrame invokedAbstrFrame = preEval.getCurrentStackFrame();
        final StackFrame invokingAbstrFrame = preEvalCallStack.get(1);

        final IMethod invokedMethod = invokedAbstrFrame.getMethod();
        final StackFrame invokedInstFrame = new StackFrame(invokedMethod);
        final StackFrame invokingInstFrame = preEvalInst.getCurrentStackFrame();
        preEvalInst.addFrame(invokedInstFrame);

        /*
        * We only increment the program counter in the invoking stack frame when doing the return, but this is not
        * needed if this a return from an exception object constructor:
        */
        final ArrayList<AbstractVariableReference> curInstInvokingOpStack =
            invokingInstFrame.getOperandStack().getStack();

        final ParsedMethodDescriptor invokedMethodDesc = invokedMethod.getMethodIdentifier().getDescriptor();
        //Remove return value (top of operand stack), if the method is non-void:
        if (invokedMethodDesc.getReturnType() != null) {
            curInstInvokingOpStack.remove(curInstInvokingOpStack.size() - 1);
        }

        /*
         * Copy values from local variables of the abstract version into the newly
         * created stack frame of the concrete one:
         */
        final LocalVariables curAbstrInvokedLocVars = invokedAbstrFrame.getLocalVariables();
        final LocalVariables curInstInvokedLocVars = invokedInstFrame.getLocalVariables();
        for (int i = 0; i < curAbstrInvokedLocVars.getSize(); i++) {
            if (curAbstrInvokedLocVars.getLocalVariable(i) != null) {
                curInstInvokedLocVars.setLocalVariable(
                    i,
                    State.mapOrCopyRef(preEval, preEvalInst, curAbstrInvokedLocVars.getLocalVariable(i), refMap));
            }
        }

        //Same for operand stack entries:
        final ArrayList<AbstractVariableReference> curAbstrInvokedOpStack =
            invokedAbstrFrame.getOperandStack().getStack();
        final ArrayList<AbstractVariableReference> curInstInvokedOpStack =
            invokedInstFrame.getOperandStack().getStack();

        for (int i = 0; i < curAbstrInvokedOpStack.size(); i++) {
            curInstInvokedOpStack.add(
                i,
                State.mapOrCopyRef(preEval, preEvalInst, curAbstrInvokedOpStack.get(i), refMap));
        }

        //Set class init state to running if the method returned from is a class initialzer
        if (invokedMethod.isClassInitializer()) {
            final ClassName cn = invokedMethod.getClassName();
            preEvalInst.getClassInitInfo().getClassesWithInitializationState(preEval.getJBCOptions()).put(cn, InitStatus.RUNNING);
        }

        //Set the program counters:
        invokedInstFrame.setCurrentOpCode(invokedAbstrFrame.getCurrentOpCode());
        invokingInstFrame.setCurrentOpCode(invokingAbstrFrame.getCurrentOpCode());

        return preEvalInst;
    }
    /**
     * {@inheritDoc}
     */
    @Override
    public Set<OpCode> getAllPossibleSuccessors() {
        return Collections.emptySet();
    }

    @Override
    public int getNumberOfArguments() {
        return 0;
    }

    @Override
    public int getNumberOfOutputs() {
        return this.returnType == null ? 0 : 1;
    }

}
