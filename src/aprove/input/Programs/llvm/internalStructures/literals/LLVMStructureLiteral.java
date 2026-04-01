package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMStructureLiteral extends LLVMLiteral {

    /**
     * The fields of the structure.
     */
    private final ImmutableList<LLVMLiteral> elements;

    /**
     * @param type The type of the structure.
     * @param elems The fields of the structure.
     */
    public LLVMStructureLiteral(final LLVMType type, final ImmutableList<LLVMLiteral> elems) {
        super(type);
        this.elements = elems;
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
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LLVMStructureLiteral other = (LLVMStructureLiteral) obj;
        if (this.elements == null) {
            if (other.elements != null) {
                return false;
            }
        } else if (!this.elements.equals(other.elements)) {
            return false;
        }
        if (!this.getType().equals(other.getType())) {
            return false;
        }
        return true;
    }

    /**
     * @return The fields of the structure.
     */
    public ImmutableList<LLVMLiteral> getElements() {
        return this.elements;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.elements == null) ? 0 : this.elements.hashCode());
        result = prime * result + ((this.getType() == null) ? 0 : this.getType().hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("Literal of type ");
        strBuilder.append(this.getType());
        strBuilder.append("(");
        if (this.elements != null) {
            boolean first = true;
            for (final LLVMLiteral element : this.elements) {
                if (first) {
                    first = false;
                } else {
                    strBuilder.append(",");
                }
                strBuilder.append(" elementtype: ");
                strBuilder.append(element.getType());
                strBuilder.append(" elementlit: ");
                strBuilder.append(element);
            }
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("{");
        if (this.elements != null) {
            boolean first = true;
            for (final LLVMLiteral element : this.elements) {
                if (first) {
                    first = false;
                } else {
                    strBuilder.append(",");
                }
                strBuilder.append(element);
            }
        }
        strBuilder.append("}");
        return strBuilder.toString();
    }

}
