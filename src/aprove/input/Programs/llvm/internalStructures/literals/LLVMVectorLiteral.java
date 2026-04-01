package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMVectorLiteral extends LLVMLiteral {

    /**
     * The elements.
     */
    private final ImmutableList<LLVMLiteral> elements;

    /**
     * @param type The type.
     * @param elems The elements.
     */
    public LLVMVectorLiteral(LLVMType type, ImmutableList<LLVMLiteral> elems) {
        super(type);
        this.elements = elems;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LLVMVectorLiteral other = (LLVMVectorLiteral) obj;
        if (this.elements == null) {
            if (other.elements != null) {
                return false;
            }
        } else if (!this.elements.equals(other.elements)) {
            return false;
        }
        return true;
    }

    /**
     * @return The elements.
     */
    public ImmutableList<LLVMLiteral> getElements() {
        return this.elements;
    }

    /**
     * @return The number of elements.
     */
    public int getSize() {
        return this.elements.size();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.elements == null) ? 0 : this.elements.hashCode());
        return result;
    }

    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("BasicVectorLiteral");
        strBuilder.append("(");
        if (this.elements != null) {
            boolean first = true;
            for (LLVMLiteral element : this.elements) {
                if (first) {
                    first = false;
                } else {
                    strBuilder.append(",");
                }
                strBuilder.append(" elementLit: " + element);
            }
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder("<");
        if (this.elements != null) {
            boolean first = true;
            for (LLVMLiteral element : this.elements) {
                if (first) {
                    first = false;
                } else {
                    strBuilder.append(",");
                }
                strBuilder.append(element);
            }
        }
        strBuilder.append(">");
        return strBuilder.toString();
    }

}
