package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Information about reference values that were accessed in the evaluation.
 *
 * @author Marc Brockschmidt
 */
public abstract class ReferenceAccessInformation implements AccessInformation {
    /**
     *  Read or write access?
     */
    private final FieldAccessRW accessType;

    /**
     * Reference of the instance which is the target of the write
     */
    private final AbstractVariableReference accessedRef;

    /**
     * Reference of the variable which is written to the field
     */
    private final AbstractVariableReference readOrWrittenRef;

    /**
     * @param type the type of the access.
     * @param accessedR the reference that was accessed.
     * @param readOrWrittenR the reference that was read or written.
     */
    public ReferenceAccessInformation(
            final FieldAccessRW type,
            final AbstractVariableReference accessedR,
            final AbstractVariableReference readOrWrittenR) {
        this.accessType = type;
        this.accessedRef = accessedR;
        this.readOrWrittenRef = readOrWrittenR;
    }

    /**
     * @return the accessType
     */
    @Override
    public FieldAccessRW getAccessType() {
        return this.accessType;
    }

    /**
     * @return the accessedRef
     */
    @Override
    public AbstractVariableReference getAccessedRef() {
        return this.accessedRef;
    }

    /**
     * @return the readOrWrittenRef
     */
    public AbstractVariableReference getReadOrWrittenRef() {
        return this.readOrWrittenRef;
    }

    /**
     * @return true iff this is a read access.
     */
    public boolean isRead() {
        return this.accessType == FieldAccessRW.READ;
    }

    /**
     * @return true iff this is a write access.
     */
    public boolean isWrite() {
        return this.accessType == FieldAccessRW.WRITE;
    }
}
