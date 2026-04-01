package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class holds information about accesses happening to abstract
 * instances.
 *
 * @author Marc Brockschmidt
 */
public class AbstractInstanceAccessInformation extends
        InstanceAccessInformation {

    /**
     * @param type Type of the access (i.e., read or write)
     * @param ref Reference of the instance which is the target of the write
     * @param value Reference of the variable which is written to the field
     * @param classN Classname determining the the class to look at (think: class hierarchy)
     * @param fieldN Name of the field to write to
     */
    public AbstractInstanceAccessInformation(final FieldAccessRW type,
            final AbstractVariableReference ref, final AbstractVariableReference value,
            final ClassName classN, final String fieldN) {
        super(type, ref, null, value, classN, fieldN);
    }

}
