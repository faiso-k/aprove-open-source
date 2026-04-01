package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 * TODO check whether pointer literals can occur at all in LLVM - the constructor is never used in our implementation
 */
public class LLVMPointerLiteral extends LLVMLiteral {

    /**
     * The value the pointer points to.
     */
    private final LLVMLiteral pointsTo;

    /**
     * @param pointerSize The size of a pointer.
     * @param pointsToValue The value the pointer points to.
     */
    public LLVMPointerLiteral(int pointerSize, LLVMLiteral pointsToValue) {
        super(new LLVMPointerType(pointsToValue.getType(), pointerSize, null));
        // TODO find out the default address space or add address space as parameter
        this.pointsTo = pointsToValue;
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
        if (!(obj instanceof LLVMPointerLiteral)) {
            return false;
        }
        final LLVMPointerLiteral other = (LLVMPointerLiteral) obj;
        if (!this.getType().equals(other.getType())) {
            return false;
        }
        if (this.pointsTo == null) {
            if (other.pointsTo != null) {
                return false;
            }
        } else if (!this.pointsTo.equals(other.pointsTo)) {
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
        result = prime * result + ((this.getType() == null) ? 0 : this.getType().hashCode());
        result = prime * result + ((this.pointsTo == null) ? 0 : this.pointsTo.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        return this.toString();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        // TODO check why this line was here:
        // assert (false) : "There are no pointer constants.";
        return "BasicPointerLiteral  points to " + this.pointsTo;
    }
}
