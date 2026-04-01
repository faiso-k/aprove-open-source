package aprove.verification.oldframework.Bytecode.Parser.Attributes;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Representation of the LocalVariableTable attribute of code attributes in
 * Java Bytecode class files.
 * @author Marc Brockschmidt
 */
public class LocalVariableTableAttribute {
    /** The actual parsed local variable table. */
    private final LocalVariableTableEntry[] localVariableTable;

    /**
     * Creates a new instance of a code attribute.
     * @param classF parsed class file in which this method is defined.
     * @param rawData Byte array containing the yet local variable code
     *  attribute data.
     */
    public LocalVariableTableAttribute(final ParsedClassFile classF, final byte[] rawData) {
        //Decompose the raw data into usable pieces:
        int bytePos = 0;

        final int localVariableTableLength =
            (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
        bytePos += 2;
        this.localVariableTable = new LocalVariableTableEntry[localVariableTableLength];

        for (int lvtIndex = 0; lvtIndex < localVariableTableLength; lvtIndex++) {
            final int scopeStart =
                (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            final int scopeLength =
                (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;

            final int nameRefIndex =
                (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            final String name = classF.resolveStringRef(nameRefIndex);

            final int descriptorRefIndex =
                (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            final String desc = classF.resolveStringRef(descriptorRefIndex);

            final int index  =
                (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;

            this.localVariableTable[lvtIndex] =
                new LocalVariableTableEntry(scopeStart, scopeLength, index, name, desc);
        }
    }

    /**
     * @return The actual table of local variable information.
     */
    public LocalVariableTableEntry[] getTable() {
        return this.localVariableTable;
    }
}
