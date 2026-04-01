package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.literals.const_expr.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represents an LLVM instruction.
 * @author cryingshadow, nowonder, Janine Repke
 */
public abstract class LLVMInstruction implements Immutable, DOTStringAble, Exportable, LLVMIRExport {
    
    protected int debugLine = -1;
    
    /**
     * @param index The index of the line with debug information.
     */
    public LLVMInstruction(int index) {
        this.debugLine = index;
    }

    /**
     * Adds the name of the specified literal to the specified set of variable names if the literal is a variable.
     * @param vars The set of variable names.
     * @param literal The literal.
     */
    protected static void collectVariable(Collection<String> vars, LLVMLiteral literal) {
        if(literal instanceof LLVMGetElementPtrConstExpr) {
        	LLVMGetElementPtrConstExpr constGEPLit = (LLVMGetElementPtrConstExpr) literal;
        	collectVariable(vars,constGEPLit.getPointerLiteral());
        } else if (literal instanceof LLVMVariableLiteral) {
            vars.add(((LLVMVariableLiteral)literal).getName());
        }
    }

    /**
     * TODO documentation
     * @param coneVars
     */
    public abstract void addConeVariables(Set<String> coneVars);

    /**
     * Adds the program variable names occurring in this instruction to the specified collection.
     * @param vars A collection of program variable names.
     */
    public abstract void collectVariables(Collection<String> vars);

    
    /**
     * Adds the program variable names used (i.e., read) by this instruction
     * Variables that are only assigned, but not read will not occur
     * @param vars A collection of program variable names.
     */
    public abstract void collectUsedVariables(Collection<String> vars);
    
    
    /**
     * Computes a relation that (probably) holds after executing this instruction. Might return null.
     * @return The computed relation if there is one, else null.
     */
    public abstract LLVMLiteralRelation computeRelation();

    /**
     * @param pos A program position of a successor of this instruction.
     * @param conditions The return conditions of the successor at pos.
     * @param params Strategy parameters.
     * @return The return conditions at the current position which imply satisfaction of the specified return
     *         conditions.
     */
    public abstract Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    );

    /**
     * @param state The state to evaluate.
     * @param nodeNumber For debugging purposes.
     * @param proveMemorySafety indicates whether we have to prove memory safety (may override setting from LLVMParameters!)
     * @param memoryTracker must be notified when evaluating free and store about what we did. May be null, then nothing is needed to do
     * @return A set of pairs, containing the result of evaluation and a set of objects describing the changes between
     *         the input and output state. If the set is no singleton, the evaluation is a refinement.
     * @throws MemorySafetyException If memory safety cannot be proven for the evaluation of this instruction.
     * @throws UndefinedBehaviorException If it cannot be proven that the evaluation of this instruction is
     *                                    sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions cannot be proven for the evaluation of this
     *                            instruction.
     * @throws ErrorStateException If an error state is reached.
     */
    public abstract Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws MemorySafetyException, UndefinedBehaviorException, AssertionException, ErrorStateException;
    
    /**
     * @return The index of the line with debug information.
     */
    public int getDebugLine() {
        return this.debugLine;
    }

    /**
     * @return The name of the variable whose value is set (or at whose address a value is stored) in this instruction.
     *         Null if there is no such variable.
     */
    public abstract String getProducedVariable();

    /**
     * @param pos A program position.
     * @param module An LLVM module.
     * @return A list of all program positions which can be reached from the specified position.
     */
    public abstract List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module);

    /**
     * @return An output of the internally used data structures.
     */
    public abstract String toDebugString();

    /**
     * @return The set of variables in this instruction that determine
     *         termination behaviour, or the empty set if this instruction
     *         doesn't determine termination. Never returns null.
     */
    public abstract Set<String> getInterestingVariables();
    /**
     * Whether or not this instruction over-approximates its evaluation result. Returning <code>true</code>
     * does not imply over-approximation but <code>false</code> guarantees that the result is accurate
     * 
     * @param state The state on which the instruction will be evaluated 
     * @param aborter The aborter that keeps track if the result is still needed
     * @return <code>false</code> if the evaluation result is guaranteed to be no over-approximation
     */
	public abstract boolean isOverapproximation(LLVMAbstractState state, Abortion aborter);

	@Override
	public String toLLVMIR() {
		return "; PROPER LLVM IR OUTPUT NOT IMPLEMENTED: " + this.getClass().getName();
	}

}
