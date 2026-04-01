package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseVariableLiteral extends LLVMParseLiteral {

    private LLVMVariableScope scope;

    private String varName; // can be a variable name

    public LLVMParseVariableLiteral(String name, LLVMVariableScope scope) {
        this.varName = name;
        this.setScope(scope);
    }

    @Override
    public LLVMLiteral convertToAddressSpace(LLVMType bType, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        if (Globals.useAssertions) {
            assert (this.scope != null) : "Scope is null!";
        }
        switch (this.scope) {
            case GLOBAL:
                final LLVMType varType = typeDefs.get(this.varName);
                if (varType.isIntType()) {
                    return new LLVMVariableLiteral(varType, this.varName, LLVMVariableScope.GLOBAL);
                } else {
                    throw new LLVMWrongAddressSpaceTypeException(this);
                }
            case LOCAL:
                return new LLVMVariableLiteral(bType, this.varName, LLVMVariableScope.LOCAL);
            default:
                throw new LLVMWrongAddressSpaceTypeException(this);
        }
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        if (Globals.useAssertions) {
            assert (this.scope != null) : "Scope is null!";
        }
        if (expectedType.isLabelType()) {
            if (this.scope == LLVMVariableScope.LOCAL) {
                return new LLVMLabelLiteral(this.varName);
            }
            // global scope, but labels have local scope
            throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
        } else {
            final LLVMType unnamedType = expectedType.getFirstNonNamedType();
            if (unnamedType instanceof LLVMVoidType) {
                // void types can not have literals
                throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
            } else if (unnamedType instanceof LLVMOpaqueType || unnamedType instanceof LLVMMetadataType) {
                throw new UnsupportedOperationException("Opaque and metadata types are not yet supported!");
            } else if (this.scope == LLVMVariableScope.LOCAL) {
                return new LLVMVariableLiteral(expectedType, this.varName, LLVMVariableScope.LOCAL);
            } else {
                return new LLVMVariableLiteral(expectedType, this.varName, LLVMVariableScope.GLOBAL);
            }
        }
    }

    @Override
    public LLVMVariableLiteral convertToIdentifier(LLVMType type) throws LLVMWrongVariableNameTypeException {
        if (Globals.useAssertions) {
            assert (this.scope != null) : "Scope is null!";
        }
        switch (this.scope) {
            case GLOBAL:
                return new LLVMVariableLiteral(type, this.varName, LLVMVariableScope.GLOBAL);
            case LOCAL:
                return new LLVMVariableLiteral(type, this.varName, LLVMVariableScope.LOCAL);
            default:
                throw new LLVMWrongVariableNameTypeException(this);
        }
    }

    @Override
    public String convertToLabelName() throws LLVMParseException {
        if (this.scope == LLVMVariableScope.LOCAL) {
            return this.varName;
        }
        // label names have LOCAL scope
        throw new LLVMWrongLabelTypeException(this);
    }

    public String getName() {
        return this.varName;
    }

    public LLVMVariableScope getScope() {
        return this.scope;
    }

    public void setName(String name) {
        this.varName = name;
    }

    public void setScope(LLVMVariableScope scope) {
        this.scope = scope;
    }

    @Override
    public String toString() {
        return this.scope.toString() + " " + this.varName;
    }

}
