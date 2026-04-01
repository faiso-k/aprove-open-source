package aprove.input.Programs.llvm.utils;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * Comparator for comparing variables in LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMVariableComparator implements Comparator<Variable> {

    /**
     * Comparator for comparing variable names.
     */
    private final Comparator<String> nameComp;

    /**
     * @param nameComp Comparator for comparing variable names.
     */
    public LLVMVariableComparator(Comparator<String> nameComp) {
        this.nameComp = nameComp;
    }

    @Override
    public int compare(Variable o1, Variable o2) {
        return this.nameComp.compare(o1.getName(), o2.getName());
    }

}
