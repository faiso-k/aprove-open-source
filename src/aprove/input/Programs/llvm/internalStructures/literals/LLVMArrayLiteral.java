package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 * TODO documentation (what is this literal exactly for? completely known arrays?)
 */
public class LLVMArrayLiteral extends LLVMLiteral {

    /**
     * The list of elements of this array.
     */
    private final ImmutableList<LLVMLiteral> elements;

    /**
     * @param elems The list of elements.
     * @param type The type of this array.
     */
    public LLVMArrayLiteral(ImmutableList<LLVMLiteral> elems, LLVMType type) {
        super(new LLVMArrayType(type, elems.size()));
        if (Globals.useAssertions) {
            for (LLVMLiteral elem : elems) {
                assert (elem.getType().equals(type)) : "Array element type does not match expected type!";
            }
        }
        this.elements = elems;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
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
        LLVMArrayLiteral other = (LLVMArrayLiteral) obj;
        if (!this.getType().equals(other.getType())) {
            return false;
        }
        if (!this.elements.equals(other.elements)) {
            return false;
        }
        return true;
    }

    /**
     * @return The elements of this array as a list.
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
        result = prime * result + this.getType().hashCode();
        result = prime * result + this.elements.hashCode();
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("Literal of type ");
        strBuilder.append(this.getType());
        strBuilder.append("[");
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
        strBuilder.append("]");
        return strBuilder.toString();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("(");
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
        strBuilder.append(")");
        return strBuilder.toString();
    }

}
