package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;

/**
 * Base class for all assignment operations. Takes care of e.g. deleting
 * heap knowledge when variable is changed.
 * @author petersk, cryingshadow
 */
public abstract class LLVMAssignmentInstruction extends LLVMInstruction {

    /**
     * The variable to be assigned; null for return type 'void' in function calls.
     */
    private final LLVMVariableLiteral identifier;

    /**
     * @param id The variable to be assigned.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMAssignmentInstruction(LLVMVariableLiteral id, int debugLine) {
        super(debugLine);
        this.identifier = id;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.instructions.BasicInstruction#addConeVariables(java.util.Set)
     */
    @Override
    public void addConeVariables(Set<String> coneVars) {
        if (this.identifier != null) {
            String name = this.identifier.getName();
            if (coneVars.contains(name)) {
                coneVars.remove(name);
                this.collectVariables(coneVars);
            }
        }
    }

    /**
     * @return The variable to be assigned.
     */
    public LLVMVariableLiteral getIdentifier() {
        return this.identifier;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.internalStructures.instructions.BasicInstruction#getProducedVariable()
     */
    @Override
    public String getProducedVariable() {
        if (this.identifier != null) {
            return this.identifier.getName();
        }
        return null;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.instructions.BasicInstruction#getSuccessors(aprove.input.Programs.llvm.generalStructures.ProgramPosition, aprove.input.Programs.llvm.basicStructures.LLVMModule)
     */
    @Override
    public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
        // FIXME this is wrong for call!
        return Collections.singletonList(new LLVMProgramPosition(pos.x, pos.y, pos.z + 1));
    }

}
