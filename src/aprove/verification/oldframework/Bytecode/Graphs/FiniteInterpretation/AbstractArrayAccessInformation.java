package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Convenience class to mark evaluation edges of abstract array access
 * operations.
 * @author Marc Brockschmidt
 */
public class AbstractArrayAccessInformation extends ArrayAccessInformation {
    /**
     * @param type Type of the access (i.e., read or write)
     * @param ref Reference of the instance which is the target of the write
     * @param value Reference of the variable which is written to the field
     * @param indexR Reference to the variable holding the accessed array index.
     */
    public AbstractArrayAccessInformation(final FieldAccessRW type,
        final AbstractVariableReference ref,
        final AbstractVariableReference value,
        final AbstractVariableReference indexR) {
        super(type, ref, value, indexR);
    }
}
