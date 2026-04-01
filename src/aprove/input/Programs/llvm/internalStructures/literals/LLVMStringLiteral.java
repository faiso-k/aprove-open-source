package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 * String literals can occur as specifier for sections. They do not occur as values to operate on with normal LLVM
 * instructions.
 */
public class LLVMStringLiteral extends LLVMLiteral {

    /**
     * The value.
     */
    private final String stringValue;

    /**
     * @param str The value.
     */
    public LLVMStringLiteral(final String str) {
        super(new LLVMStringType());
        this.stringValue = str;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMStringLiteral)) {
            return false;
        }
        final LLVMStringLiteral other = (LLVMStringLiteral) obj;
        if (this.stringValue == null) {
            if (other.stringValue != null) {
                return false;
            }
        } else if (!this.stringValue.equals(other.stringValue)) {
            return false;
        }
        return true;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.stringValue == null) ? 0 : this.stringValue.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final String str = "BasicString \"" + this.stringValue + "\"";
        return str;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.stringValue;
    }

}
