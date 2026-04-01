package aprove.verification.oldframework.Bytecode.Intersector;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Just a wrapper for Pair<State, AVR> with nice debug output.
 * @author cotto
 */
@SuppressWarnings("serial")
public class StateAndRef extends Pair<State, AbstractVariableReference> {
    /**
     * For some states remember a readable debug string.
     */
    private static final Map<State, String> STATE_DESC;

    static {
        if (Globals.DEBUG_COTTO) {
            STATE_DESC = new LinkedHashMap<State, String>();
        } else {
            STATE_DESC = null;
        }
    }

    /**
     * @param stateDesc a debug string that is shown instead of key's toString
     */
    public StateAndRef(final State key, final AbstractVariableReference value, final String stateDesc) {
        this(key, value);
        if (Globals.DEBUG_COTTO) {
            StateAndRef.STATE_DESC.put(key, stateDesc);
        }
    }

    public StateAndRef(final State key, final AbstractVariableReference value) {
        super(key, value);
    }

    @Override
    public String toString() {
        if (Globals.DEBUG_COTTO && StateAndRef.STATE_DESC.containsKey(this.x)) {
            return new Pair<String, AbstractVariableReference>(StateAndRef.STATE_DESC.get(this.x), this.y).toString();
        }
        return super.toString();
    }
}
