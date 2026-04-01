/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import org.json.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A stack frame is a frame in the call stack and contains local information,
 * e.g. the local variables and the operand stack.
 * @author cotto
 */
public class StackFrame implements Cloneable {
    /**
     * The current operand stack.
     */
    private OperandStack operandStack;

    /**
     * The local variable array.
     */
    private LocalVariables localVariables;

    /**
     * The opcode at which this specific StackFrame existed.
     */
    private OpCode currentOpcode;

    /**
     * The method corresponding to this frame.
     */
    private final IMethod method;

    /**
     * If this field is set, evaluation of the state must handle the exception
     * instead of evaluating the opcode.
     */
    private AbstractVariableReference exception;

    /**
     * The input references.
     */
    private InputReferences inputReferences;

    /**
     * Constructs a fresh stack frame when a new method is invoked.
     * @param m the started method
     */
    public StackFrame(final IMethod m) {
        this.method = m;
        // Create an operandstack.
        // Use the statically known maximum height of the operand stack
        this.operandStack = new OperandStack(this.method.getOpStackHeight());
        // Create empty local variables.
        // The amount is also statically known.
        this.setLocalVariables(new LocalVariables(this.method.getVarArrayLength()));
        // Set first instruction.
        this.currentOpcode = this.method.getStart();
        this.exception = null;
        this.inputReferences = new InputReferences();
        // Note that the inital local variables are not yet known at this point.
        // They will be set up later
    }

    /**
     * Constructs a fresh stack frame for the given opcode.
     * @param currentOpCode the current opcode
     * @param opStackSize the size of the operand stack at this position
     */
    public StackFrame(final OpCode currentOpCode, final int opStackSize) {
        this.method = currentOpCode.getMethod();
        this.setLocalVariables(new LocalVariables(this.method.getVarArrayLength()));
        this.currentOpcode = currentOpCode;
        this.operandStack = new OperandStack(this.method.getOpStackHeight(), opStackSize);
        this.exception = null;
        this.inputReferences = new InputReferences();
    }

    /**
     * Returns a deep (!) copy of this {@link StackFrame} object.
     * @return Deep copy of this object
     */
    @Override
    public final StackFrame clone() {
        StackFrame clone;

        try {
            clone = (StackFrame) super.clone();
        } catch (final CloneNotSupportedException e) {
            // This should never, ever happen:
            // super is java.lang.Object - if that one isn't cloneable,
            // we are really in deep trouble
            return null;
        }
        clone.operandStack = this.operandStack.clone();
        clone.localVariables = this.localVariables.clone();
        clone.inputReferences = this.inputReferences.clone();
        //clone.currentOpcode = this.currentOpcode;
        //clone.exception = this.exception;
        if (Globals.useAssertions) {
            assert this.currentOpcode == clone.currentOpcode;
            assert this.exception == clone.exception;
        }

        return clone;
    }

    /**
     * Returns an abstract variable referenced by an index in the local variable
     * array of the StackFrame.
     * @param index position of the variable to get
     * @return the referenced variable
     */
    public final AbstractVariableReference getLocalVariable(final int index) {
        return this.localVariables.getLocalVariable(index);
    }

    /**
     * Sets an abstract variable referenced by an index in the local variable
     * array of the StackFrame.
     * @param index position of the variable to set
     * @param var the variable to set
     */
    public final void setLocalVariable(final int index, final AbstractVariableReference var) {
        this.localVariables.setLocalVariable(index, var);
    }

    /**
     * Returns the top of the operand stack of this StackFrame.
     * @return top of the operand stack
     */
    public final AbstractVariableReference popOperandStack() {
        return this.operandStack.pop();
    }

    /**
     * Push an operand to the operand stack of this (Call)StackFrame.
     * @param ref Variable to push
     */
    public final void pushOperandStack(final AbstractVariableReference ref) {
        assert (ref != null);
        this.operandStack.push(ref);
    }

    /**
     * Look at the element on the operand stack without removing it.
     * @param index position (counted from the stack top) of the element to be
     * returned
     * @return element of the operand stack
     */
    public final AbstractVariableReference peekOperandStack(final int index) {
        return this.operandStack.peek(index);
    }

    /**
     * @return operand stack
     */
    public final OperandStack getOperandStack() {
        return this.operandStack;
    }

    /**
     * @return current OpCode
     */
    public final OpCode getCurrentOpCode() {
        return this.currentOpcode;
    }

    /**
     * @return an object representing the local variable array
     */
    public final LocalVariables getLocalVariables() {
        return this.localVariables;
    }

    /**
     * @param oStack the operandStack to set
     */
    public final void setOperandStack(final OperandStack oStack) {
        this.operandStack = oStack;
    }

    /**
     * @param lVariables the localVariables to set
     */
    public final void setLocalVariables(final LocalVariables lVariables) {
        this.localVariables = lVariables;
    }

    /**
     * @param cOpCode the currentOpCode to set
     */
    public final void setCurrentOpCode(final OpCode cOpCode) {
        assert (cOpCode != null);
        this.currentOpcode = cOpCode;
    }

    /**
     * This method stores for each abstract variable reference how often the
     * corresponding variable is used inside the state.
     * @param res the map holding the result
     */
    public final void getReferences(final Map<AbstractVariableReference, Integer> res) {
        this.getReferences(res, true);
    }

    /**
     * This method stores for each abstract variable reference how often the
     * corresponding variable is used inside the state.
     * @param res the map holding the result
     * @param withIRs iff true regard the input references of this stack frame
     */
    public final void getReferences(final Map<AbstractVariableReference, Integer> res, final boolean withIRs) {
        if (this.exception != null) {
            res.put(this.exception, res.get(this.exception) + 1);
        }
        if (withIRs) {
            this.inputReferences.getReferences(res);
        }
        this.getOperandStack().getReferences(res);
        this.getLocalVariables().getReferences(res, this.method, this.currentOpcode.getPos());
    }

    /**
     * @return a textual representation of the stack frame, where single
     * occurences of an abstract variable are shown inline.
     */
    @Override
    public String toString() {
        return this.toString(null, null, true, true);
    }

    /**
     * Seperates elements of the stackframe.
     */
    private static String SEPERATOR = "||";

    /**
     * Text prefix for the thrown exceptions.
     */
    private static String EXCEPTION_PREFIX = "Thrown exception: ";

    /**
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param state current state
     * @param detail true iff the stackframe is important so that we should
     * print a lot of detail.
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return a textual representation of the stack frame, where single
     * occurences of an abstract variable are shown inline.
     */
    public final String toString(
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean detail,
        final boolean shortRepresentation)
    {
        final StringBuilder t = new StringBuilder();

        this.inputReferences.toString(t, varUsers, state, shortRepresentation);

        t.append("<");
        // Note: I redesigned the toString method to be easier to parse.
        // This includes static variables which can be reused in parse

        // Exception?
        String prettyException;
        if (this.exception != null) {
            prettyException = PrettyVariablePrinter.prettyPrint(this.exception, varUsers, state, shortRepresentation);
            t.append(StackFrame.EXCEPTION_PREFIX).append(prettyException).append(StackFrame.SEPERATOR);
        }

        // Methodname
        // We will print the shortest unique identifier.

        final String shortestName = this.method.toShortestIdentifier(null);
        t.append(shortestName).append(StackFrame.SEPERATOR);

        // opcode
        t.append(this.currentOpcode.getPos()).append(": ");
        t.append(this.currentOpcode.toString(detail));
        t.append(StackFrame.SEPERATOR);
        // local variable array
        if (this.getLocalVariables().somethingSet()) {
            final String locVarString = this.getLocalVariables().toString(varUsers, state, this, shortRepresentation);
            if (locVarString.length() > 0) {
                t.append(locVarString).append(StackFrame.SEPERATOR);
            } else {
                t.append(" - ").append(StackFrame.SEPERATOR);
            }
        } else {
            t.append(" - ").append(StackFrame.SEPERATOR);
        }
        // operand stack
        if (!this.getOperandStack().getStack().isEmpty()) {
            t.append(this.getOperandStack().toString(varUsers, state, shortRepresentation));
        } else {
            t.append(" -");
        }

        t.append(">");
        return t.toString();
    }

    /**
     * Return the numbers of active local variables at the current opcode of the
     * stackframe.
     * @return List of active variable numbers
     */
    public Collection<Integer> getActiveVariables() {
        final Collection<Integer> vars = this.currentOpcode.getMethod().getActiveVariables(this.currentOpcode.getPos());
        for (final Iterator<Integer> it = vars.iterator(); it.hasNext();) {
            if (this.getLocalVariable(it.next()) == null) {
                it.remove();
            }
        }
        return vars;
    }

    /**
     * Replace every Abstract Variable Reference by the given new reference.
     * @param oldRef the reference that should be replaced
     * @param newRef the replacement reference
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        if (oldRef.equals(this.exception)) {
            this.exception = newRef;
        }
        this.inputReferences.replaceReference(oldRef, newRef);
        this.operandStack.replaceReference(oldRef, newRef);
        this.localVariables.replaceReference(oldRef, newRef);
    }

    /**
     * @return the method
     */
    public IMethod getMethod() {
        return this.method;
    }

    /**
     * Mark that the given exception has to be handled in this state.
     * @param ref a reference to some exception
     */
    public void setException(final AbstractVariableReference ref) {
        assert (ref != null);
        assert (this.exception == null);
        this.exception = ref;
    }

    /**
     * @return true iff this state has an exception that must be handled.
     */
    public boolean hasException() {
        return this.exception != null;
    }

    /**
     * @return the exception that must be handled
     */
    public AbstractVariableReference getException() {
        assert (this.exception != null);
        return this.exception;
    }

    /**
     * We handled the exception. No need to remember it anymore.
     */
    public void unsetException() {
        this.exception = null;
    }

    public int getId() {
        return this.getCurrentOpCode().getId();
    }

    /**
     * Initialize the local variables. Copy (i.e, using peek) the arguments from
     * the supplied OperandStack and initialize the inputReferences to
     * <code>TRUE</code> for every argument.
     * @param opStack source operand stack for fetch the local variables from
     */
    public void initLocalVariables(final OperandStack opStack) {
        // copy arguments from stack to local variable array
        final ParsedMethodDescriptor descriptor = this.method.getDescriptor();
        int index = descriptor.getArgumentWords();
        final boolean isStatic = this.method.isStatic();
        if (isStatic) {
            // We must use local var[0] for an argument (no "this")
            index -= 1;
        }

        final int argumentCount = descriptor.getArgumentCount();
        for (int i = 0; i < argumentCount; i++) {
            final int usedWords = descriptor.getType(argumentCount - i - 1).getUsedWords();
            final AbstractVariableReference ref = opStack.peek(i);
            this.setLocalVariable(index - (usedWords - 1), ref);
            index -= usedWords;
        }

        if (!isStatic) {
            // push object reference "this" on which to perform the invocation:
            final AbstractVariableReference ref = opStack.peek(descriptor.getArgumentCount());
            this.setLocalVariable(0, ref);
        }
    }

    /**
     * @return the references known in this stack frame
     */
    public Collection<AbstractVariableReference> getReferences() {
        final Map<AbstractVariableReference, Integer> map = new DefaultValueMap<>(Integer.valueOf(0));
        this.getReferences(map);
        return map.keySet();
    }

    /**
     * @return the input references
     */
    public InputReferences getInputReferences() {
        return this.inputReferences;
    }

    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Program Position", this.currentOpcode.toJSON());
        res.put("Local Variables", this.localVariables.toJSON());
        res.put("Operand Stack", this.operandStack.toJSON());
        if (this.exception != null) {
            res.put("Exception", this.exception.toString());
        }
        return res;
    }
}
