package aprove.input.Programs.llvm.internalStructures;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;

/**
 * Condition for removing trap values.
 * @author cryingshadow
 * @version $Id$
 */
public interface LLVMTrapCondition extends HasVariables, Immutable, Substitutable {

    @Override
    default LLVMTrapCondition applySubstitution(Variable var, Expression exp) {
        return (LLVMTrapCondition)this.applySubstitution(Collections.singletonMap(var, exp));
    }

    @Override
    Set<? extends LLVMSymbolicVariable> getVariables();

    /**
     * @param state Some abstract LLVM state.
     * @return A flag and a state. The flag is true iff the condition for removing the trap value is satisfied. The
     *         state is the specified state possibly updated during the association checks.
     */
    Pair<Boolean, LLVMAbstractState> resolved(LLVMAbstractState state, Abortion aborter);

}
