package aprove.input.Programs.llvm.internalStructures.module;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * Is list of instructions with an optional name. A function definition contains blocks.
 * @author Janine Repke, CryingShadow
 */
public class LLVMBasicBlock implements Immutable, DOTStringAble, Exportable, LLVMIRExport {

    /**
     * The label name.
     */
    private final String blockName;

    /**
     * The instructions in this basic block.
     */
    private final ImmutableList<LLVMInstruction> instructions;

    /**
     * @param labelName The label name.
     * @param instructionList The instructions in this basic block.
     */
    public LLVMBasicBlock(String labelName, ImmutableList<LLVMInstruction> instructionList) {
        this.blockName = labelName;
        this.instructions = instructionList;
    }

    /**
     * Adds the program positions occurring in this basic block to the specified collection.
     * @param functionName The name of the function this basic block belongs to.
     * @param poss A collection of program positions.
     */
    public void collectAllPositions(String functionName, Collection<LLVMProgramPosition> poss) {
        final String block = this.getBlockName();
        for (int line = 0; line < this.getInstructions().size(); line++) {
            poss.add(new LLVMProgramPosition(functionName, block, line));
        }
    }

    /**
     * Adds the program variable names occurring in this basic block to the specified collection.
     * @param vars A collection of program variable names.
     */
    public void collectAllProgramVariableNames(Collection<String> vars) {
        for (LLVMInstruction instr : this.getInstructions()) {
            instr.collectVariables(vars);
        }
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
        LLVMBasicBlock other = (LLVMBasicBlock) obj;
        if (this.blockName == null) {
            if (other.blockName != null) {
                return false;
            }
        } else if (!this.blockName.equals(other.blockName)) {
            return false;
        }
        return true;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (LLVMInstruction instruction : this.instructions) {
            if (first) {
                first = false;
            } else {
                res.append(eu.linebreak());
            }
            res.append(instruction.export(eu));
        }
        return eu.tttext(this.blockName + ":") + eu.linebreak() + eu.indent(res.toString());
    }

    /**
     * @return The label name.
     */
    public String getBlockName() {
        return this.blockName;
    }

    /**
     * @return The instructions in this basic block.
     */
    public ImmutableList<LLVMInstruction> getInstructions() {
        return this.instructions;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.blockName == null) ? 0 : this.blockName.hashCode());
        return result;
    }

    @Override
    public String toDOTString() {
        return this.blockName;
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("\t" + this.blockName + ":\n");
        for (LLVMInstruction instruction : this.instructions) {
            strBuilder.append("\t\t" + instruction.toString() + "\n");
        }
        return strBuilder.toString();
    }

	public String toLLVMIR() {
		StringBuilder str = new StringBuilder(this.blockName + ":\n");
		this.instructions.stream().forEach(i -> str.append("  " + i.toLLVMIR() + "\n"));
		return str.toString();
	}

}
