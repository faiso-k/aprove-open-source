package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMShuffleVectorInstruction extends LLVMAssignmentInstruction {

    /**
     * The shuffle mask for element selection (as for the type, only the length is interesting - the elements must be
     * of type i32).
     */
    private final LLVMLiteral maskLiteral;

    /**
     * The first vector.
     */
    private final LLVMLiteral vector1Literal;

    /**
     * The second vector.
     */
    private final LLVMLiteral vector2Literal;

    /**
     * @param id The variable to assign the result vector to.
     * @param vec1 The first vector.
     * @param vec2 The second vector.
     * @param mask The shuffle mask for element selection (as for the type, only the length is interesting - the
     *             elements must be of type i32).
     * @param debugLine The index of the line with debug information.
     */
    public LLVMShuffleVectorInstruction(LLVMVariableLiteral id, LLVMLiteral vec1, LLVMLiteral vec2, LLVMLiteral mask, int debugLine) {
        super(id, debugLine);
        if (Globals.useAssertions) {
            assert (vec1.getType().equals(vec2.getType())) : "Both vectors must have the same type!";
            assert (mask.getType().isVectorType()) : "Mask is no vector!";
            assert (mask.getType().getThisAsVectorType().getElementType().isIntTypeOfSize(32)) :
                "Elements of mask are not i32!";
        }
        this.vector1Literal = vec1;
        this.vector2Literal = vec2;
        this.maskLiteral = mask;
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.maskLiteral);
        LLVMInstruction.collectVariable(vars, this.vector1Literal);
        LLVMInstruction.collectVariable(vars, this.vector2Literal);
    }
    
    public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        return null;
    }

    @Override
    public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    ) {
        // TODO
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Not yet implemented.");
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public String export(Export_Util eu) {
        return this.toString();
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /**
     * @return The shuffle mask for element selection (as for the type, only the length is interesting - the elements
     *         must be of type i32).
     */
    public LLVMLiteral getMaskLiteral() {
        return this.maskLiteral;
    }

    /**
     * @return The first vector.
     */
    public LLVMLiteral getVector1Literal() {
        return this.vector1Literal;
    }

    /**
     * @return The second vector.
     */
    public LLVMLiteral getVector2Literal() {
        return this.vector2Literal;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("ShuffleVectorInstr ");
        strBuilder.append(" identifier:" + this.getIdentifier());
        strBuilder.append(" valueType: " + this.vector1Literal.getType());
        strBuilder.append(" value1Lit: " + this.vector1Literal);
        strBuilder.append(" value2Lit: " + this.vector2Literal);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toDOTString());
        res.append(" = shufflevector ");
        res.append(this.maskLiteral.toDOTString());
        res.append(", ");
        res.append(this.vector1Literal.toDOTString());
        res.append(", ");
        res.append(this.vector2Literal.toDOTString());
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toString());
        res.append(" = shufflevector ");
        res.append(this.maskLiteral.toString());
        res.append(", ");
        res.append(this.vector1Literal.toString());
        res.append(", ");
        res.append(this.vector2Literal.toString());
        return res.toString();
    }

}
