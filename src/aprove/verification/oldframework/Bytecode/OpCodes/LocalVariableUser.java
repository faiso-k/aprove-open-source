package aprove.verification.oldframework.Bytecode.OpCodes;

/**
 * Interface implemented by all opcodes which directly access the local
 * variable array of a stackframe.
 *
 * @author Marc Brockschmidt
 */
public interface LocalVariableUser {
    /**
     * @return index of the accessed local variable.
     */
    int getUsedLocalVariableIndex();
}
