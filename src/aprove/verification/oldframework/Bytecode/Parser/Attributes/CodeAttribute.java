package aprove.verification.oldframework.Bytecode.Parser.Attributes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Representation of the Code attribute of methods in Java Bytecode class
 * files.
 * @author Marc Brockschmidt
 */
public class CodeAttribute {
    /** The maximal height of the operand stack in this method. */
    private final int maxStackHeight;

    /** The maximal index into the local variable array used in this method. */
    private final int maxLocalVarNumber;

    /** The actual raw bytecode. */
    private final byte[] bytecode;

    /** The exception handler table for this method. */
    private final ExceptionTableEntry[] exceptionHandlerTable;

    /** Further attributes for this method. */
    private final Attribute[] attributes;

    /** The unparsed local variable table attribute. */
    private Attribute rawLocalVariableTableAttr;

    /** The local variable table attribute. */
    private LocalVariableTableAttribute localVariableTableAttr;

    /** Parsed class file in which this method is defined. */
    private final ParsedClassFile classFile;

    /**
     * Creates a new instance of a code attribute.
     * @param classF parsed class file in which this method is defined.
     * @param rawData Byte array containing the yet unparsed code attribute data.
     */
    public CodeAttribute(final ParsedClassFile classF, final byte[] rawData) {
        this.classFile = classF;

        //Decompose the raw data into usable pieces:
        int bytePos = 0;
        this.maxStackHeight = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
        bytePos += 2;
        this.maxLocalVarNumber = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
        bytePos += 2;
        final int codeL = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 4);
        bytePos += 4;
        this.bytecode = new byte[codeL];
        System.arraycopy(rawData, bytePos, this.bytecode, 0, codeL);
        bytePos += codeL;

        //This is the number of exception handlers:
        final int exceptionTableL = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
        bytePos += 2;
        //Each exception table entry takes up 4 shorts = 8 bytes
        this.exceptionHandlerTable = new ExceptionTableEntry[exceptionTableL];
        for (int excHIndex = 0; excHIndex < exceptionTableL; excHIndex++) {
            final int startPos = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            final int endPos = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            final int handlerPos = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            final int handledTypeIndex = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
            bytePos += 2;
            ClassName handledType;
            if (handledTypeIndex != 0) {
                handledType = this.classFile.resolveClassNameRef(handledTypeIndex);
            } else {
                handledType = JAVA_LANG_OBJECT.getClassName();
            }
            this.exceptionHandlerTable[excHIndex] = new ExceptionTableEntry(startPos, endPos, handlerPos, handledType);
        }

        final int attributeCount = (int) ParsedClassFile.getUSignedFromByteArray(rawData, bytePos, 2);
        bytePos += 2;
        this.attributes = this.classFile.parseAttributes(attributeCount, rawData, bytePos);

        for (final Attribute a : this.attributes) {
            if (a.getAttributeName().equals("LocalVariableTable")) {
                this.rawLocalVariableTableAttr = a;
            }
        }
    }

    /**
     * @return The actual raw bytecode.
     */
    public byte[] getBytecode() {
        return this.bytecode;
    }

    /**
     * @return The maximal index into the local variable array used in this method.
     */
    public int getMaxLocalVarNumber() {
        return this.maxLocalVarNumber;
    }

    /**
     * @return The maximal height of the operand stack in this method.
     */
    public int getMaxStackHeight() {
        return this.maxStackHeight;
    }

    /**
     * @return The exception handler table for this method.
     */
    public ExceptionTableEntry[] getExceptionHandlerTable() {
        return this.exceptionHandlerTable;
    }

    /**
     * @return The local variable table attribute.
     */
    public LocalVariableTableAttribute getLocalVariableTableAttribute() {
        if (this.localVariableTableAttr == null && this.rawLocalVariableTableAttr != null) {
            this.localVariableTableAttr =
                new LocalVariableTableAttribute(this.classFile, this.rawLocalVariableTableAttr.getUnparsedData());
        }
        return this.localVariableTableAttr;
    }
}
