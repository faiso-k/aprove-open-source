package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMLabelLiteral extends LLVMLiteral {

    /**
     * The label name.
     */
    private final String labelName;

    /**
     * @param label The label name.
     */
    public LLVMLabelLiteral(final String label) {
        super(new LLVMLabelType());
        this.labelName = label;
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof LLVMLabelLiteral) {
            final LLVMLabelLiteral label = (LLVMLabelLiteral) obj;
            return (this.labelName.equals(label.labelName));
        }
        return false;
    }

    /**
     * @return The label name.
     */
    public String getLabelName() {
        return this.labelName;
    }

    @Override
    public int hashCode() {
        final int prime = 7;
        int result = 2;
        result = prime * result + ((this.labelName == null) ? 0 : this.labelName.hashCode());
        return result;
    }

    @Override
    public String toDebugString() {
        final String str = "BasicLabel labelName: " + this.labelName;
        return str;
    }

    @Override
    public String toString() {
        return this.labelName;
    }

}
