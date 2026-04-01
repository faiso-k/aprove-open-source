package aprove.input.Programs.llvm.internalStructures;

import immutables.*;

/**
 * A pair (x,y) encoding the index x of the allocation to which a term is associated to and a boolean flag y stating
 * whether this association points exactly one cell behind the allocation.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMAssociationIndex extends ImmutablePair<Integer, Boolean> {

    /**
     * @param index The index of the associated allocation.
     * @param oneMore True iff the associated term points exactly to one cell behind the allocation.
     */
    public LLVMAssociationIndex(Integer index, Boolean oneMore) {
        super(index, oneMore);
    }

}
