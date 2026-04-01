package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * Generic formatter for the output of variables.
 *
 * @author Marc Brockschmidt
 */
public final class PrettyVariablePrinter {
    /**
     * Default constructor, not to be called.
     */
    private PrettyVariablePrinter() {
        assert (false) : "Thou shall not instantiate me!";
    }

    /**
     * @param varRef Reference of the variable to be formatted
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param state current state
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return String representation of this {@link ConcreteInstance}.
     */
    public static String prettyPrint(
        final AbstractVariableReference varRef,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation) {

        final StringBuilder t = new StringBuilder();

        if (varUsers != null && state != null) {
            //If the var is of a primitive type and this is the only usage of this
            //variable, print it here:
            final AbstractVariable v = state.getAbstractVariable(varRef);
            if (v instanceof AbstractNumber) {
                if (shortRepresentation
                    && (varUsers.containsKey(varRef) && varUsers.get(varRef) == 1 || (((AbstractNumber) v).isLiteral()))) {
                    t.append(v.toString());
                } else {
                    t.append(varRef.toString());
                }
            } else {
                t.append(varRef.toString());
            }

            if (state.getHeapAnnotations().isMaybeExisting(varRef)) {
                t.append("?");
            }
        } else {
            t.append(varRef.toString());
        }
        return t.toString();
    }

}
