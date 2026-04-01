package aprove.verification.oldframework.Bytecode.Parser.Attributes;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Exception table entries collect information about exception handlers, storing which
 * positions they cover, the class of the handled exceptions and the opcode which
 * handles them.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class ExceptionTableEntry {
    /**
     * Position in the bytecode array of the first opcode handled by this entry.
     */
    private final int start;

    /**
     * Position in the bytecode array of the last opcode handled by this entry.
     */
    private final int end;

    /**
     * Class of the handled exceptions.
     */
    private final ClassName handledExceptionClass;

    /**
     * Position of first Opcode of the exception handler.
     */
    private final int handlerPosition;

    /**
     * @param startPos Position in the bytecode array of the first opcode handled by this entry.
     * @param endPos Position in the bytecode array of the last opcode handled by this entry.
     * @param handlerPos First Opcode of the exception handler.
     * @param handledExceptionC Class of the handled exceptions.
     */
    public ExceptionTableEntry(final int startPos,
            final int endPos,
            final int handlerPos,
            final ClassName handledExceptionC) {
        this.start = startPos;
        this.end = endPos;
        this.handledExceptionClass = handledExceptionC;
        this.handlerPosition = handlerPos;
    }

    /**
     * @return Position of first Opcode of the exception handler.
     */
    public int getHandlerPosition() {
        return this.handlerPosition;
    }

    /**
     * @return Class of the handled exceptions.
     */
    public ClassName getHandledExceptionClass() {
        return this.handledExceptionClass;
    }

    /**
     * Check if a given opcode position is handled by this exception table
     * entry.
     *
     * @param index Opcode position in the method
     * @return true iff this exception table entry is actually handling this
     *  opcode
     */
    public boolean posIsHandled(final int index) {
        return (index >= this.start && index <= this.end);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.handledExceptionClass + " (" + this.start + ", " + this.end + ")";
    }
}
