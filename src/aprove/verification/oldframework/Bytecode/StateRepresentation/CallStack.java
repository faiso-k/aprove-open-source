/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.*;

/**
 * The call stack represents the single stack frames of each invoked method. For
 * recursive programs the call stack may get very huge.
 * @author cotto
 */
public class CallStack implements Cloneable {
    /**
     * The individual stack frames.
     */
    private ArrayList<StackFrame> callStack;

    /**
     * Creates an empty call stack
     */
    public CallStack() {
        this.callStack = new ArrayList<StackFrame>();
    }

    /**
     * Returns a deep (!) copy of this {@link CallStack} object.
     * @return Deep copy of this object
     */
    @Override
    public CallStack clone() {
        CallStack clone;
        try {
            clone = (CallStack) super.clone();
        } catch (final CloneNotSupportedException e) {
            // This should never, ever happen:
            // super is java.lang.object - if that one isn't cloneable,
            // we are really in deep trouble
            return null;
        }

        final ArrayList<StackFrame> clonedCallStack = new ArrayList<StackFrame>();
        for (int i = 0; i < this.callStack.size(); i++) {
            clonedCallStack.add(this.callStack.get(i).clone());
        }
        clone.callStack = clonedCallStack;

        return clone;
    }

    /**
     * @param index position (from the top) of the stackframe to return
     * @return the requested {@link StackFrame}
     */
    public final StackFrame get(final int index) {
        if (this.callStack.size() > index) {
            return this.callStack.get(index);
        }
        return null;
    }

    /**
     * @param index position (from the bottom) of the stackframe to return, starting at 1 (and not 0!)
     * @return the requested {@link StackFrame}
     */
    public final StackFrame getFromBottom(final int index) {
        return this.callStack.get(this.callStack.size()-index);
    }

    /**
     * Get topmost {@link StackFrame} on this callstack.
     * @return topmost {@link StackFrame}
     */
    public StackFrame getTop() {
        if (!this.isEmpty()) {
            return this.get(0);
        }
        return null;
    }

    /**
     * Removes the topmost element from the stack and returns it.
     * @return topmost stackframe
     */
    public StackFrame pop() {
        return this.callStack.remove(0);
    }

    /**
     * Adds a new frame at the top of the stack
     * @param newFrame Frame to add
     */
    public void push(final StackFrame newFrame) {
        this.callStack.add(0, newFrame);
    }

    /**
     * @return a textual representation of the call stack.
     */
    @Override
    public String toString() {
        return this.toString(null, null, true);
    }

    /**
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param state current state
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return a textual representation of the call stack, where single
     * occurences of an abstract variable are shown inline.
     */
    public String toString(final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation) {
        final StringBuilder t = new StringBuilder();
        final Iterator<StackFrame> it = this.callStack.iterator();
        boolean first = true;
        while (it.hasNext()) {
            final StackFrame f = it.next();
            final String stackFrameString = f.toString(varUsers, state, first, shortRepresentation);
            t.append(stackFrameString);
            first = false;
            if (it.hasNext()) {
                t.append("\n");
            }
        }
        return t.toString();
    }

    /**
     * @return true iff there is no frame on the callstack
     */
    public boolean isEmpty() {
        return this.callStack.isEmpty();
    }

    /**
     * Do not modify the list!
     * @return the encapsulated List of {@link AbstractStackFrame} objects
     */
    public List<StackFrame> getStackFrameList() {
        return this.callStack;
    }

    /**
     * This method stores for each abstract variable reference how often the
     * corresponding variable is used inside the state.
     * @param res the map holding the result
     */
    public final void getReferences(
            final Map<AbstractVariableReference, Integer> res) {
        for (int i = 0; i < this.callStack.size(); i++) {
            this.callStack.get(i).getReferences(res);
        }
    }

    /**
     * @param opCode some opcode
     * @return how often the given opcode appears on the stack
     */
    public int getOpCodeCounter(final OpCode opCode) {
        int res = 0;
        for (final StackFrame sf : this.callStack) {
            if (sf.getCurrentOpCode().equals(opCode)) {
                res++;
            }
        }
        return res;
    }

    /**
     * Returns the number of {@link StackFrame} objects on this
     * {@link CallStack}.
     * @return the number of {@link StackFrame} objects
     */
    public final int size() {
        return this.callStack.size();
    }

    /**
     * Replace every Abstract Variable Reference by the given new reference.
     * @param oldRef the reference that should be replaced
     * @param newRef the replacement reference
     */
    public void replaceReference(final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef) {
        for (final StackFrame sf : this.callStack) {
            sf.replaceReference(oldRef, newRef);
        }
    }

    /**
     * Delete all stack frames.
     */
    public void clear() {
        this.callStack.clear();
    }

    /**
     * Push all stack frames from the given stack
     * @param stack some call stack
     */
    public void pushAll(final CallStack stack) {
        this.callStack.addAll(0, stack.callStack);
    }

    /**
     * @param other another stack
     * @return true iff the two stacks have the same shape when disregarding all
     * recovery information
     */
    public boolean hasSameOuterShape(final CallStack other) {
        final int size = this.size();
        if (other.size() != size) {
            return false;
        }
        for (int i = 0; i < size; i++) {
            final StackFrame frameOne = this.get(i);
            final StackFrame frameTwo = other.get(i);
            if (!frameOne.getCurrentOpCode().equals(frameTwo.getCurrentOpCode())) {
                return false;
            }
            final boolean hasExceptionOne = frameOne.hasException();
            final boolean hasExceptionTwo = frameTwo.hasException();
            if (hasExceptionOne != hasExceptionTwo) {
                return false;
            }
        }
        return true;
    }

    /**
     * Remove all but the topmost stackframe.
     */
    public void abstractToTopStackFrame() {
        final StackFrame top = this.getTop();
        this.callStack.clear();
        this.callStack.add(top);
    }

    /**
     * @return JSON representation of this object.
     */
    public JSONArray toJSON() throws JSONException {
        final JSONArray res = new JSONArray();
        for (StackFrame sf : this.callStack) {
            res.put(sf.toJSON());
        }
        return res;
    }
}
