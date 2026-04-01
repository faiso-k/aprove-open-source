package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * When executing a JSR (JSR_W) opcode, a value of type returnAddress is pushed
 * onto the operand stack. This value cannot be changed. Only the RET opcode can
 * see the value itself. The ASTORE opcode that is used to store the opcode into
 * a local variable just moves the reference (which, in this case, is the
 * address itself).
 * @author cotto
 */
public class ReturnAddress extends AbstractVariableReference {

    /**
     * The OpCode to return to.
     */
    private final OpCode opCode;

    /**
     * Create a new ReturnAddress for the given opcode.
     * @param opCodeParam some opcode.
     */
    public ReturnAddress(final OpCode opCodeParam) {
        super("RA " + opCodeParam.getPos(), OperandType.RETURN_ADDRESS);
        this.opCode = opCodeParam;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result =
            prime * result
                + ((this.opCode == null) ? 0 : this.opCode.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ReturnAddress other = (ReturnAddress) obj;
        if (this.opCode == null) {
            if (other.opCode != null) {
                return false;
            }
        } else if (!this.opCode.equals(other.opCode)) {
            return false;
        }
        return true;
    }

    /**
     * @return the opcode
     */
    public OpCode getOpCode() {
        return this.opCode;
    }
}
