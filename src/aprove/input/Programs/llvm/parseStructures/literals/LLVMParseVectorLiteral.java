package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class LLVMParseVectorLiteral extends LLVMParseLiteral {

    private final List<Pair<LLVMParseType, LLVMParseLiteral>> elements;

    public LLVMParseVectorLiteral() {
        this.elements = new ArrayList<Pair<LLVMParseType, LLVMParseLiteral>>();
    }

    public void addElement(Pair<LLVMParseType, LLVMParseLiteral> element) {
        this.elements.add(element);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        if (expectedType.isVectorType()) {
            final LLVMVectorType vectorType = expectedType.getThisAsVectorType();
            if (Globals.useAssertions) {
                assert (vectorType.getLength() == this.getSize()) : "Number of elements does not match expected type!";
            }
            final LLVMType elementType = vectorType.getElementType();
            // convert elements
            final List<LLVMLiteral> elems = new ArrayList<LLVMLiteral>();
            for (Pair<LLVMParseType, LLVMParseLiteral> element : this.elements) {
                if (Globals.useAssertions) {
                    assert (elementType.equals(element.x.convertToBasicType(typeDefs, pointerSize))) :
                        "Expected element type does not match specified element type!";
                }
                elems.add(element.y.convertToBasicLiteral(elementType, unsigned, typeDefs, pointerSize));
            }
            return new LLVMVectorLiteral(expectedType, ImmutableCreator.create(elems));
        } else {
            throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
        }
    }

    public List<Pair<LLVMParseType, LLVMParseLiteral>> getElements() {
        return this.elements;
    }

    public int getSize() {
        return this.elements.size();
    }

    @Override
    public String toString() {
        return "Vector: " + this.elements.toString();
    }

}
