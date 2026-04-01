package aprove.input.Programs.llvm.internalStructures;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import immutables.*;

/**
 * A pair (x,y) encoding a memory access at address x where the corresponding pointer has type y.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMSimpleMemoryAccess extends ImmutablePair<LLVMTerm, LLVMPointerType> {

    /**
     * @param term The term.
     * @param type The type of the term.
     */
    public LLVMSimpleMemoryAccess(LLVMTerm term, LLVMPointerType type) {
        super(term, type);
    }

}
