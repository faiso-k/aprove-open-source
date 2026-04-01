package aprove.input.Programs.llvm.utils;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Comparator for comparing integer relations in LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMRelationComparator implements Comparator<IntegerRelation> {

    /**
     * Comparator for comparing variables.
     */
    private final Comparator<Variable> varComp;

    /**
     * @param vComp Comparator for comparing variables.
     */
    public LLVMRelationComparator(Comparator<Variable> vComp) {
        this.varComp = vComp;
    }

    @Override
    public int compare(IntegerRelation o1, IntegerRelation o2) {
        List<Variable> refList1 = new ArrayList<Variable>(o1.getVariables());
        List<Variable> refList2 = new ArrayList<Variable>(o2.getVariables());
        if (refList1.isEmpty()) {
            if (refList2.isEmpty()) {
                return 0;
            }
            return -1;
        } else if (refList2.isEmpty()) {
            return 1;
        }
        Collections.sort(refList1, this.varComp);
        Collections.sort(refList2, this.varComp);
        return this.varComp.compare(refList1.get(0), refList2.get(0));
    }

}
