package aprove.input.Programs.llvm.internalStructures;

import org.json.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Convenience class for return information in the call stack. It contains the old variable mapping, the old program
 * position, and the allocations made in that function.
 * @author cryingshadow, Frank Emrich
 * @version $Id$
 */
public class LLVMReturnInformation implements Immutable, JSONExport {

    /**
     * The allocations made in the function.
     */
    private final ImmutableTreeSet<Integer> allocationsInFunction;

    /**
     * The program position to return to.
     */
    private final LLVMProgramPosition progPos;

    /**
     * The local variables in the function.
     */
    private final ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable,LLVMType>> variableFunction;

    /**
     * @param variableFunction The variable function.
     * @param pos The program position.
     * @param allocationsInFuntion Set of indices of allocations which were made in this function
     */
    public LLVMReturnInformation(
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> variableFunction,
        LLVMProgramPosition pos,
        ImmutableTreeSet<Integer> allocationsInFuntion
    ) {
        this.variableFunction = variableFunction;
        this.progPos = pos;
        this.allocationsInFunction = allocationsInFuntion;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LLVMReturnInformation other = (LLVMReturnInformation)obj;
        return
            this.variableFunction.equals(other.variableFunction)
            && this.progPos.equals(other.progPos)
            && this.allocationsInFunction.equals(other.allocationsInFunction);
    }

    /**
     * @return The allocations made in the function.
     */
    public ImmutableTreeSet<Integer> getAllocationsInFunction() {
        return this.allocationsInFunction;
    }

    /**
     * @return The program position to return to.
     */
    public LLVMProgramPosition getProgPos() {
        return this.progPos;
    }

    /**
     * @return The local program variables in the function.
     */
    public ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> getProgramVariables() {
        return this.variableFunction;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result +  this.variableFunction.hashCode();
        result = prime * result +  this.progPos.hashCode();
        result = prime * result +  this.allocationsInFunction.hashCode();
        return result;
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", "StackFrame");
        res.put("variables", JSONExportUtil.toJSON(this.getProgramVariables()));
        res.put("pos", JSONExportUtil.toJSON(this.getProgPos()));
        res.put("allocations", JSONExportUtil.toJSON(this.getAllocationsInFunction()));
        return res;
    }

}
