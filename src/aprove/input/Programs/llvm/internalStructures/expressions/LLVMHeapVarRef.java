package aprove.input.Programs.llvm.internalStructures.expressions;

/**
 * This kind of reference is used as pattern variable for return conditions (encoding heap accesses).
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMHeapVarRef extends LLVMHeuristicVarRef {

    /**
     * @param nameParam The varaible's name.
     * @param dName The variable's debug name.
     * @param type The type of this reference.
     */
    public LLVMHeapVarRef(String nameParam, String dName) {
        super(nameParam, dName);
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
        if (!(obj instanceof LLVMHeapVarRef)) {
            return false;
        }
        LLVMHeapVarRef other = (LLVMHeapVarRef)obj;
        if (this.getName() == null) {
            if (other.getName() != null) {
                return false;
            }
        } else if (!this.getName().equals(other.getName())) {
            return false;
        }
        return true;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 37;
        int result = 3;
        result = prime * result + ((this.getName() == null) ? 0 : this.getName().hashCode());
        return result;
    }

}
