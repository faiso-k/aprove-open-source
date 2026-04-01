package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * A named type which represents a type, but may has to be resolved later.
 */
public class LLVMParseNamedType extends LLVMParseType {

    private String typeName;

    /**
     * @param name Name of the type without leading %-sign.
     */
    public LLVMParseNamedType(String name) {
        this.setTypeName(name);
    }

    @Override
    public boolean checkIfTypeIsIntType(LLVMModule basicModule) throws LLVMParseException {
        return basicModule.getTypeDefinitions().get(this.typeName).isIntType();
    }

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        return module.getTypeDefinition(this.typeName).checkIfTypeIsPrimitiveType(module);
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return false;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        return new LLVMNamedType(this.typeName, typeDefs.get(this.typeName));
    }

    public String getTypeName() {
        return this.typeName;
    }

    public void setTypeName(String name) {
        this.typeName = name;
    }

    @Override
    public String toString() {
        return this.typeName;
    }

}
