package aprove.input.Programs.llvm.internalStructures.expressions;

/**
 * This kind of reference is used as pattern variable for return conditions.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMProgVarRef extends LLVMSymbolicVariable {

    /**
     * @param nameParam The variable's name.
     * @param dName The variable's debug name.
     */
    public LLVMProgVarRef(String nameParam, String dName) {
        super(nameParam, dName);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMProgVarRef)) {
            return false;
        }
        final LLVMProgVarRef other = (LLVMProgVarRef)obj;
        if (this.getName() == null) {
            if (other.getName() != null) {
                return false;
            }
        } else if (!this.getName().equals(other.getName())) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 23;
        int result = 7;
        result = prime * result + ((this.getName() == null) ? 0 : this.getName().hashCode());
        return result;
    }

}
