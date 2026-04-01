package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMInvokeInstruction extends LLVMAssignmentInstruction {

    /**
     * The calling convention (optional - maybe null).
     */
    private final LLVMCallingConvention callConv;

    /**
     * The label reached when a callee returns with the unwind instruction.
     */
    private final String exceptionLabel;

    /**
     * The function attributes.
     */
    private final ImmutableList<LLVMFunctionAttribute> functionAttributes;

    /**
     * The name of the function to invoke.
     */
    private final LLVMVariableLiteral functionName;

    /**
     * The function parameters.
     */
    private final ImmutableList<ImmutablePair<LLVMFnParameter, LLVMLiteral>> functionParameters;

    /**
     * The label reached when the called function executes a 'ret' instruction.
     */
    private final String normalLabel;

    /**
     * The return type of the called function.
     */
    private final LLVMFnParameter returnType;

    /**
     * @param id The variable to assign the result of the function invocation to (maybe null for void functions).
     * @param conv The calling conventions.
     * @param attrs The function attributes.
     * @param type The return type of the function.
     * @param name The name of the function.
     * @param params The function parameters.
     * @param normal The label reached when the called function executes a 'ret' instruction.
     * @param exception The label reached when a callee returns with the unwind instruction.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMInvokeInstruction(
        LLVMVariableLiteral id,
        LLVMCallingConvention conv,
        ImmutableList<LLVMFunctionAttribute> attrs,
        LLVMFnParameter type,
        LLVMVariableLiteral name,
        ImmutableList<ImmutablePair<LLVMFnParameter, LLVMLiteral>> params,
        String normal,
        String exception,
        int debugLine
    ) {
        super(id, debugLine);
        this.callConv = conv;
        this.functionAttributes = attrs;
        this.returnType = type;
        this.functionName = name;
        this.functionParameters = params;
        this.normalLabel = normal;
        this.exceptionLabel = exception;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        vars.add(this.functionName.getName());
        for (ImmutablePair<LLVMFnParameter, LLVMLiteral> arg : this.functionParameters) {
            LLVMInstruction.collectVariable(vars, arg.y);
        }
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

    /**
     * @return The calling convention.
     */
    public LLVMCallingConvention getCallConv() {
        return this.callConv;
    }

    /**
     * @return The label reached when a callee returns with the unwind instruction.
     */
    public String getExceptionLabel() {
        return this.exceptionLabel;
    }

    /**
     * @return The function attributes.
     */
    public ImmutableList<LLVMFunctionAttribute> getFunctionAttributes() {
        return this.functionAttributes;
    }

    /**
     * @return The name of the function.
     */
    public LLVMVariableLiteral getFunctionName() {
        return this.functionName;
    }

    /**
     * @return The function parameters.
     */
    public ImmutableList<ImmutablePair<LLVMFnParameter, LLVMLiteral>> getFunctionParameters() {
        return this.functionParameters;
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /**
     * @return The label reached when the called function executes a 'ret' instruction.
     */
    public String getNormalLabel() {
        return this.normalLabel;
    }

    /**
     * @return The return type of the function.
     */
    public LLVMFnParameter getReturnType() {
        return this.returnType;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("CallInstr ");
        strBuilder.append(" identifier: ");
        strBuilder.append(this.getIdentifier());
        strBuilder.append(" callConv: ");
        strBuilder.append(this.callConv);
        strBuilder.append(" returnType: ");
        strBuilder.append(this.returnType);
        strBuilder.append(" fnName: ");
        strBuilder.append(this.functionName);
        boolean first = true;
        strBuilder.append(" parameters: (");
        for (ImmutablePair<LLVMFnParameter, LLVMLiteral> pair : this.functionParameters) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" ");
            strBuilder.append("(type: ");
            strBuilder.append(pair.x);
            strBuilder.append(", value: ");
            strBuilder.append(pair.y);
            strBuilder.append(")");
        }
        strBuilder.append(")");
        strBuilder.append(" fnAttributes: (");
        first = true;
        for (LLVMFunctionAttribute fnAttribute : this.functionAttributes) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" ");
            strBuilder.append(fnAttribute);
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        // TODO: implement a more detailed output
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public String toString() {
        // TODO: implement a more detailed output
        return "invoke ... not implemented yet";
    }

}
