package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import org.json.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Representation of the local variable array of a stack frame.
 * @author Marc Brockschmidt
 */
public class LocalVariables implements Cloneable {
    /**
     * Actual array holding the variable references.
     */
    private AbstractVariableReference[] localVariables;

    /**
     * Creates a fresh representation of a local variable array.
     * @param localVariableNumber maximal number of used variables
     */
    public LocalVariables(final int localVariableNumber) {
        this.localVariables =
            new AbstractVariableReference[localVariableNumber];
    }

    /**
     * Returns a deep (!) copy of this {@link LocalVariables} object.
     * @return Deep copy of this object
     */
    @Override
    public LocalVariables clone() {
        LocalVariables clone;
        try {
            clone = (LocalVariables) super.clone();
        } catch (final CloneNotSupportedException e) {
            // This should never, ever happen:
            // super is java.lang.object - if that one isn't cloneable,
            // we are really in deep trouble
            return null;
        }

        final AbstractVariableReference[] locVars =
            new AbstractVariableReference[this.localVariables.length];

        for (int i = 0; i < this.localVariables.length; i++) {
            if (this.localVariables[i] != null) {
                locVars[i] = this.localVariables[i].clone();
            }
        }
        clone.setLocalVariables(locVars);

        return clone;
    }

    /**
     * @return size of the local variable array
     */
    public final int getSize() {
        return this.localVariables.length;
    }

    /**
     * @return the localVariables
     */
    public AbstractVariableReference[] getLocalVariables() {
        return this.localVariables;
    }

    /**
     * @param localVars the localVariables to set
     */
    public void setLocalVariables(final AbstractVariableReference[] localVars) {
        this.localVariables = localVars;
    }

    /**
     * @param index Index of the variable to get
     * @return {@link AbstractVariableReference} to the value of the variable to get
     */
    public AbstractVariableReference getLocalVariable(final int index) {
        return this.localVariables[index];
    }

    /**
     * @param index Index of the variable to set
     * @param ref {@link AbstractVariableReference} to the value of the variable to get
     */
    public void setLocalVariable(final int index,
        final AbstractVariableReference ref) {
        this.localVariables[index] = ref;
    }

    /**
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param state current state
     * @param stackFrame the current stack frame
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return a textual representation of the stack frame, where single
     * occurences of an abstract variable are shown inline.
     */
    public String toString(final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final StackFrame stackFrame,
        final boolean shortRepresentation) {
        int frameNum = 0;
        if (Globals.DEBUG_COTTO && state != null) {
            for (final StackFrame frame : state.getCallStack().getStackFrameList()) {
                if (frame == stackFrame) {
                    break;
                }
                frameNum++;
            }
        }
        final StringBuilder t = new StringBuilder();
        int opcodePos = -1;
        IMethod method = null;
        Collection<Integer> activeList = new LinkedList<Integer>();
        if (stackFrame != null) {
            opcodePos = stackFrame.getCurrentOpCode().getPos();
            method = stackFrame.getMethod();
            activeList = method.getActiveVariables(opcodePos);
        } else {
            for (int i = 0; i < this.localVariables.length; i++) {
                activeList.add(i);
            }
        }
        boolean first = true;
        for (final int i : activeList) {
            if (this.localVariables[i] != null) {
                if (!first) {
                    t.append(", ");
                }
                first = false;
                this.appendName(t, method, i, opcodePos, frameNum);
                t.append(": "
                    + PrettyVariablePrinter.prettyPrint(this.localVariables[i], varUsers, state, shortRepresentation));
            }
        }
        return t.toString();
    }

    /**
     * Append a readable representation of the name of the local variable.
     * @param sb a string builder
     * @param index the index of the local variable
     * @param method the method defining the local variable
     * @param opcodePos the position of the current opcode
     * @param frameNum the index of the current stack frame in the callstack
     */
    private void appendName(final StringBuilder sb,
        final IMethod method,
        final int index,
        final int opcodePos,
        final int frameNum) {
        String name = null;
        if (method != null) {
            name = method.getLocalVariableName(index, opcodePos);
        }
        if (name == null) {
            sb.append("#");
            sb.append(index);
        } else {
            sb.append(name);
        }
        if (Globals.DEBUG_COTTO && !Globals.DEBUG_MARC) {
            final StatePosition pos =
                LocVarRootPosition.create(frameNum, index);
            sb.append("(");
            sb.append(pos.toString());
            sb.append(")");
        }
    }

    @Override
    public String toString() {
        return this.toString(null, null, null, true);
    }

    /**
     * This method stores for each abstract variable reference how often the
     * corresponding variable is used inside the state.
     * @param res the map holding the result
     * @param method the method of the corresponding stack frame
     * @param opcodePos the current opcode position
     */
    public void getReferences(final Map<AbstractVariableReference, Integer> res,
        final IMethod method,
        final int opcodePos) {
        final Collection<Integer> activeVars =
            method.getActiveVariables(opcodePos);
        for (final int i : activeVars) {
            final AbstractVariableReference locVar = this.localVariables[i];
            if (locVar != null) {
                res.put(locVar, res.get(locVar) + 1);
            }
        }
    }

    /**
     * @return true iff there is a defined value in the local variable array
     */
    public boolean somethingSet() {
        for (final AbstractVariableReference localVariable : this.localVariables) {
            if (localVariable != null) {
                return true;
            }
        }
        return false;
    }

    /**
     * Replace every Abstract Variable Reference by the given new reference.
     * @param oldRef the reference that should be replaced
     * @param newRef the replacement reference
     */
    public void replaceReference(final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef) {
        for (int pos = 0; pos < this.localVariables.length; pos++) {
            final AbstractVariableReference someRef = this.localVariables[pos];
            if (oldRef.equals(someRef)) {
                this.localVariables[pos] = newRef;
            }
        }
    }

    /**
     * @return all abstract variable references
     * @param method the current method
     * @param opcodePos the current position in the method
     */
    public Collection<AbstractVariableReference> getAbstractVariableReferences(final IMethod method,
        final int opcodePos) {
        final Collection<AbstractVariableReference> result =
            new LinkedList<AbstractVariableReference>();
        final Collection<Integer> activeVars =
            method.getActiveVariables(opcodePos);
        for (final int i : activeVars) {
            final AbstractVariableReference locVar = this.localVariables[i];
            if (locVar != null) {
                result.add(locVar);
            }
        }
        return result;
    }

    public JSONArray toJSON() throws JSONException {
        final JSONArray res = new JSONArray();
        for (AbstractVariableReference ref : this.localVariables) {
            if (ref != null) {
                res.put(ref.toString());
            } else {
                res.put(ref);
            }
        }
        return res;
    }
}
