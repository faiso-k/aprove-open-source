package aprove.input.Programs.llvm.utils;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import immutables.*;

/**
 * Comparator for comparing variables in LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMSimpleTermPairComparator implements Comparator<ImmutablePair<LLVMSimpleTerm, LLVMSimpleTerm>> {

    /**
     * Comparator for comparing variable names.
     */
    private final Comparator<String> nameComp;

    /**
     * @param nameComp Comparator for comparing variable names.
     */
    public LLVMSimpleTermPairComparator(Comparator<String> nameComp) {
        this.nameComp = nameComp;
    }

    @Override
    public int compare(
        ImmutablePair<LLVMSimpleTerm, LLVMSimpleTerm> o1,
        ImmutablePair<LLVMSimpleTerm, LLVMSimpleTerm> o2
    ) {
        return this.nameComp.compare(o1.x.getName(), o2.x.getName());
    }

}
