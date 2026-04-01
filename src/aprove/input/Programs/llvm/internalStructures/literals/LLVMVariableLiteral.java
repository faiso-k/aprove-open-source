package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMVariableLiteral extends LLVMLiteral implements IntegerVariable {

    /**
     * The variable's name without leading % or @ sign.
     */
    private final String name;

    /**
     * The scope of the variable.
     */
    private final LLVMVariableScope scope;

    /**
     * @param type The type of the variable.
     * @param varName The variable's name without leading % or @ sign.
     * @param varScope The scope of the variable.
     */
    public LLVMVariableLiteral(LLVMType type, String varName, LLVMVariableScope varScope) {
        super(type);
        this.name = varName;
        this.scope = varScope;
    }

    @Override
    public long convertToLength(LLVMModule basicModule) throws LLVMParseException {
        // TODO: Later: also check if this name is an alias
        // check if variable is global
        if (this.scope == LLVMVariableScope.GLOBAL) {
            // check if type of variable is integer
            LLVMGlobalVariable variable = basicModule.getVariableDefinitions().get(this.name);
            if (variable.getType() instanceof LLVMIntType) {
                // determine value
                return variable.getInitValue().convertToLength(basicModule);
            }
        }
        throw new LLVMWrongLengthValueException(this.getType());
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
        LLVMVariableLiteral other = (LLVMVariableLiteral) obj;
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        if (this.scope != other.scope) {
            return false;
        }
        return true;
    }

    @Override
    public BigInteger evaluate(Map<LLVMLiteral, BigInteger> varToVal) {
        return varToVal.containsKey(this) ? varToVal.get(this) : null;
    }

    /**
     * @return Name with leading %- or @-symbol.
     */
    @Override
    public String getName() {
        switch (this.scope) {
        case GLOBAL:
            return "@" + this.name;
        case LOCAL:
            return "%" + this.name;
        default:
            throw new IllegalStateException("Each variable should have a scope.");
        }
    }

    /**
     * @return Name without leading %- or @-symbol.
     */
    public String getNameWithoutScope() {
        return this.name;
    }

    /**
     * @return The scope of the variable.
     */
    public LLVMVariableScope getScope() {
        return this.scope;
    }

    @Override
    public Set<LLVMVariableLiteral> getVariables() {
        return Collections.singleton(this);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        result = prime * result + ((this.scope == null) ? 0 : this.scope.hashCode());
        return result;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("BasicVariableName");
        strBuilder.append(" \"" + this.getName() + "\"");
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        return this.getName();
    }

    @Override
    public LLVMHeuristicTerm transformToLLVMHeuristicTerm(
        Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef,
        LLVMHeuristicTermFactory factory
    ) {
        return varToRef.containsKey(this) ? varToRef.get(this) : null;
    }

}
