package aprove.input.Programs.llvm.internalStructures.module;

import aprove.input.Programs.llvm.internalStructures.*;

/**
 * @param <T> The type of the objects to create.
 * @author cryingshadow
 * @version $Id$
 */
public interface LLVMInstructionGraphNodeObjectCreator<T> {

    /**
     * @param prog An LLVM module.
     * @param pos A program position.
     * @return An object of type T to be the node object for the specified position.
     */
    T create(LLVMModule prog, LLVMProgramPosition pos);

}