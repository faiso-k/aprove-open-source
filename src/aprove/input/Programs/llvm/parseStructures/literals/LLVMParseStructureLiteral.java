package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class LLVMParseStructureLiteral extends LLVMParseLiteral {

    private final List<Pair<LLVMParseType, LLVMParseLiteral>> elements;

    public LLVMParseStructureLiteral() {
        this.elements = new ArrayList<Pair<LLVMParseType, LLVMParseLiteral>>();
    }

    public void addElement(Pair<LLVMParseType, LLVMParseLiteral> element) {
        this.elements.add(element);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        if (expectedType.getFirstNonNamedType() instanceof LLVMStructureType) {
            final LLVMStructureType structureType = (LLVMStructureType) expectedType.getFirstNonNamedType();
            if (Globals.useAssertions) {
                assert (structureType.getNumberOfFields() == this.elements.size()) :
                    "Number of elements does not match expected type!";
            }
            final List<LLVMLiteral> elems = new ArrayList<LLVMLiteral>();
            final Iterator<LLVMType> elemTypes = structureType.getElementTypes().iterator();
            for (Pair<LLVMParseType, LLVMParseLiteral> element : this.elements) {
                final LLVMType expectedElemType = elemTypes.next();
//                if (Globals.useAssertions) {
//                    assert (expectedElemType.equals(element.x.convertToBasicType(typeDefs, pointerSize))) :
//                        "Expected element type does not match specified element type!";
//                }
                elems.add(element.y.convertToBasicLiteral(expectedElemType, unsigned, typeDefs, pointerSize));
            }
            return new LLVMStructureLiteral(expectedType, ImmutableCreator.create(elems));
        } else {
            throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
        }
    }

    public List<Pair<LLVMParseType, LLVMParseLiteral>> getElements() {
        return this.elements;
    }

    @Override
    public String toString() {
        return "Struct: " + this.elements.toString();
    }

}
