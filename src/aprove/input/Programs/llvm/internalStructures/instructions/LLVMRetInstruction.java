package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Return from a function.
 *
 * @author Janine Repke, CryingShadow
 */
public class LLVMRetInstruction extends LLVMTerminatorInstruction {

	/**
	 * The return value (for void functions this is null).
	 */
	private final LLVMLiteral returnLiteral;

	/**
	 * @param value     The return value (for void functions this is null).
	 * @param debugLine The index of the line with debug information.
	 */
	public LLVMRetInstruction(LLVMLiteral value, int debugLine) {
		super(debugLine);
		this.returnLiteral = value;
	}

	@Override
	public void addConeVariables(Set<String> coneVars) {
		LLVMInstruction.collectVariable(coneVars, this.returnLiteral);
	}

	@Override
	public final void collectVariables(Collection<String> vars) {
		if (this.returnLiteral != null) {
			LLVMInstruction.collectVariable(vars, this.returnLiteral);
		}
	}

	@Override
	public void collectUsedVariables(Collection<String> vars) {
		collectVariables(vars);
	}

	@Override
	public LLVMLiteralRelation computeRelation() {
		return null;
	}

	@Override
	public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(LLVMProgramPosition pos,
			Set<Pair<IntegerRelationSet, List<String>>> conditions, LLVMParameters params) {
		// we do not need to add anything here as this instruction should already have a
		// sufficient condition
		// TODO what about recursion?
		return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
	}

	@Override
	public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber,
			boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter) {
		if (state.getCallStack().isEmpty()) {
			throw new IllegalStateException("The last return statement should mark the end!");
		}
		LLVMAbstractState retState = state.popCallStack(aborter);
		LLVMInstruction instr = retState.getCurrentInstruction();
		retState = retState.incrementPC();

		if (Globals.useAssertions) {
			assert (instr instanceof LLVMCallInstruction);
		}
		LLVMCallInstruction call = (LLVMCallInstruction) instr;
		if (this.returnLiteral == null) {
			// void return statement
			if (call.getIdentifier() != null) {
				throw new IllegalStateException("Found void return for non-void call!");
			}
			return Collections.singleton(new LLVMSymbolicEvaluationResult(retState, Collections.emptySet()));
		} else {
			if (call.getIdentifier() == null) {
				// return value is ignored
				return Collections.singleton(new LLVMSymbolicEvaluationResult(retState, Collections.emptySet()));
			}

			Set<LLVMRelation> newRels = new LinkedHashSet<>();

			LLVMSimpleTerm ref = state.getSimpleTermForLiteral(this.returnLiteral);
			assert call.getReturnType()
					.equals(returnLiteral.getType()) : "Returned literal does not match function return type";
			retState = retState.assign(call.getIdentifier().getName(), ref, call.getReturnType(), newRels, aborter);
			LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(retState, newRels);
			return Collections.singleton(evaluationResult);
		}
	}

	@Override
	public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
		return false;
	}

	@Override
	public String export(Export_Util eu) {
		return eu.tttext(this.returnLiteral == null ? "ret void" : "ret " + this.returnLiteral.toString());
	}

	@Override
	public Set<String> getInterestingVariables() {
		return Collections.emptySet();
	}

	@Override
	public String getProducedVariable() {
		return null;
	}

	/**
	 * @return The return value (for void functions this is null).
	 */
	public LLVMLiteral getReturnLiteral() {
		return this.returnLiteral;
	}

	/**
	 * @return The type of the return value (void if there is none).
	 */
	public LLVMType getReturnType() {
		if (this.returnLiteral == null) {
			return new LLVMVoidType();
		} else {
			return this.returnLiteral.getType();
		}
	}

	@Override
	public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
		return Collections.emptyList();
	}

	@Override
	public String toDebugString() {
		StringBuilder strBuilder = new StringBuilder("RetInstr ");
		strBuilder.append(" returnType: " + this.returnLiteral.getType());
		strBuilder.append(" returnLit: " + this.returnLiteral);
		return strBuilder.toString();
	}

	@Override
	public String toDOTString() {
		return this.returnLiteral == null ? "ret void" : "ret " + this.returnLiteral.toDOTString();
	}

	@Override
	public String toString() {
		return this.returnLiteral == null ? "ret void" : "ret " + this.returnLiteral;
	}

	@Override
    public String toLLVMIR() {
        return this.returnLiteral == null ? "ret void" : "ret " + this.getReturnType().toLLVMIR() + " " + this.returnLiteral.toLLVMIR();
    }

}
