package aprove.input.Programs.llvm.internalStructures.dataType;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMStructureType extends LLVMType {

    /**
     * The types of this structure's fields.
     */
    private final ImmutableList<LLVMType> elementTypes;

    /**
     * The packing type.
     */
    private final LLVMPackingType packingType;

    /**
     * @param packType The packing type.
     * @param elemTypes The types of this structure's fields.
     */
    public LLVMStructureType(LLVMPackingType packType, ImmutableList<LLVMType> elemTypes) {
        this.packingType = packType;
        this.elementTypes = elemTypes;
    }

    @Override
    public boolean isAggregateType() {
        return true;
    }

    @Override
    public boolean isStructureType() {
        return true;
    }

    @Override
    public List<LLVMType> getSubtypes() {
        return this.elementTypes;
    }

    @Override
    public LLVMLiteral convertToZeroInitializedLiteral(boolean unsigned) throws LLVMParseException {
        List<LLVMLiteral> elements = new ArrayList<LLVMLiteral>();
        for (LLVMType elementType : this.getElementTypes()) {
            elements.add(elementType.convertToZeroInitializedLiteral(unsigned));
        }
        return new LLVMStructureLiteral(this, ImmutableCreator.create(elements));
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
        LLVMStructureType other = (LLVMStructureType)obj;
        if (this.elementTypes == null) {
            if (other.elementTypes != null) {
                return false;
            }
        } else if (!this.elementTypes.equals(other.elementTypes)) {
            return false;
        }
        if (this.packingType != other.packingType) {
            return false;
        }
        return true;
    }

    /**
     * @return The types of this structure's fields.
     */
    public ImmutableList<LLVMType> getElementTypes() {
        return this.elementTypes;
    }

    @Override
    public AbstractBoundedInt getInitializedIntValue(boolean unsigned, boolean useBoundedIntegers) {
        // TODO implement correctly
        return AbstractBoundedInt.getUnknown(this.getIntegerType(unsigned, useBoundedIntegers));
    }

    @Override
    public IntegerType getIntegerType(boolean unsigned, boolean useBoundedIntegers) {
        // TODO implement correctly
        return IntegerType.UI64;
    }

    /**
     * @return The number of this structure's fields.
     */
    public int getNumberOfFields() {
        return this.elementTypes.size();
    }

    /**
     * @return The packing type.
     */
    public LLVMPackingType getPackingType() {
        return this.packingType;
    }

    @Override
    public LLVMType getSubtype(int index) {
        return this.elementTypes.get(index);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.elementTypes == null) ? 0 : this.elementTypes.hashCode());
        result = prime * result + ((this.packingType == null) ? 0 : this.packingType.hashCode());
        return result;
    }

    @Override
    public int size() {
        int res = 0;
        for (LLVMType type : this.elementTypes) {
            if (type.size() > 64) {
                res += type.size();
            } else {
                res += 64;
            }
        }
        return res;
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("BasicStructureType");
        strBuilder.append("(");
        if (this.elementTypes != null) {
            boolean first = true;
            for (LLVMType elementType : this.elementTypes) {
                if (first) {
                    first = false;
                } else {
                    strBuilder.append(", ");
                }
                if (elementType instanceof LLVMPointerType && ((LLVMPointerType)elementType).getTargetType().isStructureType()) {
                    strBuilder.append("elementType: *struct");
                } else if (elementType instanceof LLVMPointerType && ((LLVMPointerType)elementType).getTargetType() instanceof LLVMNamedType) {
                    strBuilder.append("elementType: *" + ((LLVMNamedType)((LLVMPointerType)elementType).getTargetType()).getTypeName());
                } else {
                    strBuilder.append("elementType: " + elementType);
                }
            }
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

}
