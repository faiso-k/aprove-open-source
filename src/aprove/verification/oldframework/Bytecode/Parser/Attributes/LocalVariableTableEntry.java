package aprove.verification.oldframework.Bytecode.Parser.Attributes;

/**
 * Representation of entries in the LocalVariableTable attribute of Java
 * Bytecode class files.
 * @author Marc Brockschmidt
 */
public class LocalVariableTableEntry {
    /** The first position in the scope of this entry. */
    private final int scopeStart;

    /** The last position in the scope of this entry. */
    private final int scopeEnd;

    /** Index in the local variable array described by this entry. */
    private final int localVarIndex;

    /** Variable name associated with this register in this scope. */
    private final String varName;

    /** Variable type associated with this register in this scope. */
    private final String varDescriptor;

    /**
     * Creates a new local variable table entry.
     * @param scopeSt Start of the scope of this entry.
     * @param scopeLength Length of this scope.
     * @param varIndex Index in the local variable array described by this entry.
     * @param varN Variable name associated with this register in this scope.
     * @param varDesc Variable type associated with this register in this scope.
     */
    public LocalVariableTableEntry(final int scopeSt, final int scopeLength, final int varIndex,
        final String varN, final String varDesc) {
        this.scopeStart = scopeSt;
        this.scopeEnd = this.scopeStart + scopeLength;
        this.localVarIndex = varIndex;
        this.varName = varN;
        this.varDescriptor = varDesc;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return this.varName + ": " + this.scopeStart + " to " + this.scopeEnd;
    }

    /**
     * @return Index in the local variable array described by this entry.
     */
    public int getLocalVarIndex() {
        return this.localVarIndex;
    }

    /**
     * @param pos Some bytecode position.
     * @return true iff the <code>pos</code> lies in the scope of this entry.
     */
    public boolean positionInScope(final int pos) {
        return (pos >= this.scopeStart && pos <= this.scopeEnd);
    }

    /**
     * @return Variable name associated with this register in this scope.
     */
    public String getVarName() {
        return this.varName;
    }
}
