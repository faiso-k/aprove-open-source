package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Representation of the operand stack of a stack frame.
 * @author Marc Brockschmidt
 */
public class OperandStack implements Cloneable {
    /**
     * Actual stack holding the data. Here, even values which would usually need
     * two 32bit cells (like longs and doubles) just take up one entry. The top-most
     * entry is the last entry of the array list.
     */
    private ArrayList<AbstractVariableReference> stack;

    /**
     * Creates a fresh (and empty) operand stack.
     * @param maxStackSize maximal size of the operand stack
     */
    public OperandStack(final int maxStackSize) {
        this.stack = new ArrayList<AbstractVariableReference>(maxStackSize);
    }

    /**
     * Creates a fresh operand stack filled with currentSize times null.
     * @param maxStackSize maximal size of the operand stack
     * @param currentSize the number of (null) entries in the stack
     */
    public OperandStack(final int maxStackSize, final int currentSize) {
        this.stack = new ArrayList<AbstractVariableReference>(maxStackSize);
        for (int i = 0; i < currentSize; i++) {
            this.stack.add(null);
        }
    }

    /**
     * Returns a deep (!) copy of this {@link OperandStack} object
     * @return Deep copy of this object
     */
    @Override
    public OperandStack clone() {
        OperandStack clone;
        try {
            clone = (OperandStack) super.clone();
        } catch (final CloneNotSupportedException e) {
            // This should never, ever happen:
            // super is java.lang.object - if that one isn't cloneable,
            // we are really in deep trouble
            return null;
        }

        final ArrayList<AbstractVariableReference> newStack = new ArrayList<AbstractVariableReference>(this.stack.size());
        for (int i = 0; i < this.stack.size(); i++) {
            if (this.stack.get(i) != null) {
                newStack.add(this.stack.get(i).clone());
            } else {
                newStack.add(null);
            }
        }
        clone.stack = newStack;
        return clone;
    }

    /**
     * @return the stack
     */
    public ArrayList<AbstractVariableReference> getStack() {
        return this.stack;
    }

    /**
     * Emulate Stack-like behavior on our OperandStack and return the
     * topmost element.
     * @return top of the operand stack
     */
    public AbstractVariableReference pop() {
        //AbstractList only looks like a proper implementation of a
        //stack, but we need to do this manually here:
        final AbstractVariableReference top = this.stack.get(this.stack.size() - 1);
        this.stack.remove(this.stack.size() - 1);
        return top;
    }

    /**
     * Return the <code>i</code>th element (from the top) of the stack.
     * @param i index of the element to have a peek at, counted starting with 0 from the stack top.
     * @return top of the operand stack
     */
    public AbstractVariableReference peek(final int i) {
        return this.stack.get(this.stack.size() - 1 - i);
    }

    /**
     * Emulate Stack-like behavior on our OperandStack and add an
     * element to the top of the stack.
     * @param var push variable to the top of the operand stack
     */
    public void push(final AbstractVariableReference var) {
        assert (var != null);
        this.stack.add(var);
    }

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
     * @return a textual representation of the operand stack, where single
     * occurences of an abstract variable are shown inline.
     */
    public String toString(
            final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation) {
        final StringBuilder t = new StringBuilder();
        //Push out stack as list, beginning with the top
        for (int i = 0; i < this.stack.size(); i++) {
            t.append(PrettyVariablePrinter.prettyPrint(this.stack.get(i), varUsers, state, shortRepresentation));
            if (i < this.stack.size() - 1) {
                t.append(", ");
            }
        }
        return t.toString();
    }

    /**
     * Set a specific position on the operand stack to a new value.
     * @param index position in the stack
     * @param var new value
     */
    public final void set(final int index, final AbstractVariableReference var) {
        assert (var != null);
        this.stack.set(this.stack.size() - 1 - index, var);
    }

    /**
     * This method stores for each abstract variable reference how often the
     * corresponding variable is used inside the state.
     * @param res the map holding the result
     */
    public void getReferences(final Map<AbstractVariableReference, Integer> res) {
        for (int i = 0; i < this.stack.size(); i++) {
            final AbstractVariableReference key = this.stack.get(i);
            res.put(key, res.get(key) + 1);
        }
    }

    /**
     * Replace every Abstract Variable Reference by the given new reference.
     * @param oldRef the reference that should be replaced
     * @param newRef the replacement reference
     */
    public void replaceReference(final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef) {
        for (int pos = 0; pos < this.stack.size(); pos++) {
            final AbstractVariableReference someRef = this.stack.get(pos);
            if (someRef.equals(oldRef)) {
                this.stack.remove(pos);
                this.stack.add(pos, newRef);
            }
        }
    }

    /**
     * @return all abstract variable references
     */
    public Collection<AbstractVariableReference> getAbstractVariableReferences() {
        final Collection<AbstractVariableReference> result =
            new LinkedList<AbstractVariableReference>();
        for (int i = 0; i < this.stack.size(); i++) {
            final AbstractVariableReference key = this.stack.get(i);
            result.add(key);
        }
        return result;
    }

    public JSONArray toJSON() throws JSONException {
        final JSONArray res = new JSONArray();
        for (AbstractVariableReference ref : this.stack) {
            res.put(ref.toString());
        }
        return res;
    }
}
