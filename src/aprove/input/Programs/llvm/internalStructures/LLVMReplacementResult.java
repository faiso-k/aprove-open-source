package aprove.input.Programs.llvm.internalStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Give pairs of abstract states and replacement maps from references to references a name.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMReplacementResult extends Pair<LLVMHeuristicState, Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 5884980682114759668L;

    /**
     * @param x The state component.
     * @param y The replacement map component.
     */
    public LLVMReplacementResult(LLVMHeuristicState x, Map<LLVMHeuristicVariable, LLVMHeuristicVariable> y) {
        super(x, y);
    }

}