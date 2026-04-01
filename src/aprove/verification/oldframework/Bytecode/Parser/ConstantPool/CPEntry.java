package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

/**
 * Abstract class from which all constant pool entry representations are derived.
 *
 * @author Marc Brockschmidt
 */
public interface CPEntry {

    /**
     * Fill the given stream with the data of this constant pool entry.
     * @param out a DataOutputStream
     * @throws IOException whenever writing fails
     */
    void writeTo(DataOutputStream out) throws IOException;
}
