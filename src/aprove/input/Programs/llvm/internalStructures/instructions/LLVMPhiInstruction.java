package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Depending on the last evaluated block, the phi instruction sets the identifier to the corresponding value. Note that
 * several consecutive phi instructions are executed atomically together. Thus, they are never executed on their own,
 * but together with a preceding terminator instruction.
 *
 * Example:
 * Phi instruction: %0 = phi i32 [ 0, %bb.nph ], [ %2, %bb ]
 * If the last block is %bb.nph, then %0 is set to 0. If the last block is %bb, %0 is set to the value of %2.
 * @author Janine Repke, CryingShadow
 */
public class LLVMPhiInstruction extends LLVMAssignmentInstruction {

    /**
     * The argument list indicating what value to assign depending on which block we come from.
     */
    private final ImmutableList<ImmutablePair<String, LLVMLiteral>> argumentPairs;

    /**
     * @param id The variable to assign the value to.
     * @param args The argument list indicating what value to assign depending on which block we come from.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMPhiInstruction(LLVMVariableLiteral id, ImmutableList<ImmutablePair<String, LLVMLiteral>> args, int debugLine) {
        super(id, debugLine);
        if (Globals.useAssertions) {
            LLVMType type = args.get(0).y.getType();
            for (ImmutablePair<String, LLVMLiteral> pair : args) {
                assert (type.equals(pair.y.getType())) : "All arguments must have the same type!";
            }
        }
        this.argumentPairs = args;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        for (ImmutablePair<String, LLVMLiteral> arg : this.argumentPairs) {
            LLVMInstruction.collectVariable(vars, arg.y);
        }
    }
    
    public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        // TODO
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
        throw new IllegalStateException("A phi instruction should never be evaluated on its own!");
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        throw new IllegalStateException("A phi instruction should never be evaluated on its own!");
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = phi "));
        boolean first = true;
        for (ImmutablePair<String, LLVMLiteral> argPair : this.argumentPairs) {
            if (first) {
                first = false;
            } else {
                res.append(eu.tttext(", "));
            }
            res.append(eu.tttext("["));
            res.append(eu.tttext(argPair.y.toString()));
            res.append(eu.tttext(", %"));
            res.append(eu.tttext(argPair.x.toString()));
            res.append(eu.tttext("]"));
        }
        return res.toString();
    }

    /**
     * @return The argument list indicating what value to assign depending on which block we come from.
     */
    public ImmutableList<ImmutablePair<String, LLVMLiteral>> getArgumentPairs() {
        return this.argumentPairs;
    }

    @Override
    public Set<String> getInterestingVariables() {
        return Collections.emptySet();
    }

    /**
     * @return The type of the value to assign.
     */
    public LLVMType getValueType() {
        return this.argumentPairs.get(0).y.getType();
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("PhiInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" valueType: " + this.getValueType());
        strBuilder.append(" Arguments: (");
        boolean first = true;
        for (ImmutablePair<String, LLVMLiteral> argPair : this.argumentPairs) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + argPair);
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        return this.toString(true);
    }

    @Override
    public String toString() {
        return this.toString(false);
    }

    /**
     * @param dot Flag indicating whether or not to produce DOT output.
     * @return A String representation of this object.
     */
    public String toString(boolean dot) {
        StringBuilder strBuilder =
            new StringBuilder(dot ? this.getIdentifier().toDOTString() : this.getIdentifier().toString());
        strBuilder.append(" = phi ");
        boolean first = true;
        for (ImmutablePair<String, LLVMLiteral> argPair : this.argumentPairs) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append("[");
            strBuilder.append(dot ? argPair.y.toDOTString() : argPair.y.toString());
            strBuilder.append(", %");
            strBuilder.append(argPair.x);
            strBuilder.append("]");
        }
        return strBuilder.toString();
    }

}
