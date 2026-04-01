package aprove.input.Programs.llvm.internalStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Give a name to liveness information.
 * @author nowonder, cryingshadow
 */
public class LLVMLiveness extends Quadruple<LLVMProgramPosition, LLVMInstruction, Set<String>, Boolean> {

    /**
     * @param pos The program position.
     * @param instruction The instruction at pos.
     * @param liveNames The names of the live variables.
     * @param needed Flag indicating whether or not the instruction is needed to prove memory safety or termination.
     */
    public LLVMLiveness(LLVMProgramPosition pos, LLVMInstruction instruction, Set<String> liveNames, Boolean needed) {
        super(pos, instruction, liveNames, needed);
    }

}
