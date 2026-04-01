package aprove.input.Programs.llvm.segraph;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * An LLVMPostProcessing contains the resulting state and the state change information.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMSymbolicEvaluationResult extends Pair<LLVMAbstractState, Set<? extends LLVMRelation>> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -4695261836381616592L;

    /**
     * @param state The state.
     * @param info The state change info.
     */
    public LLVMSymbolicEvaluationResult(LLVMAbstractState state, Set<? extends LLVMRelation> info) {
        super(state, info);
    }

    public LLVMAbstractState getState() {
        return x;
    }
    
    public void setState(LLVMAbstractState state) {
        x = state;
    }
    
    public Set<? extends LLVMRelation> getStateChangeInfo() {
        return y;
    }
    
    public void setStateChangeInfo(Set<? extends LLVMRelation> stateChangeInfo) {
        y = stateChangeInfo;
    }
}
