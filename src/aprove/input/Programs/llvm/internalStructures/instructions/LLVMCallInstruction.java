package aprove.input.Programs.llvm.internalStructures.instructions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * We support only declared functions assuming that these just return their (possibly non-deterministically) computed
 * value without modifying anything visible to the caller or unwinding an exception. This is used for nondef function
 * calls yielding arbitrarily many non-deterministic values.
 * TODO <fnty>: shall be the signature of the pointer to function value being invoked. The argument types must match
 *      the types implied by this signature. This type can be omitted if the function is not varargs and if the
 *      function type does not return a pointer to a function.
 * @author Janine Repke, CryingShadow
 */
public class LLVMCallInstruction extends LLVMAssignmentInstruction {

    /**
     * @param state The original state.
     * @return The specified state where the PC has been incremented by one and an empty set of changes.
     */
    private static Set<LLVMSymbolicEvaluationResult> noop(LLVMAbstractState state) {
        return Collections.singleton(new LLVMSymbolicEvaluationResult(state.incrementPC(), Collections.emptySet()));
    }

    /**
     * The calling convention (optional - maybe null).
     */
    private final LLVMCallingConvention callConv;

    /**
     * The attributes of the function to call.
     */
    private final ImmutableList<LLVMFunctionAttribute> functionAttributes;

    /**
     * The name of the function to call.
     */
    private final LLVMVariableLiteral functionName;

    /**
     * The parameters of the function to call.
     */
    private final ImmutableList<ImmutablePair<LLVMFnParameter, LLVMLiteral>> functionParameters;

    /**
     * The attributes of the return value.
     */
    private final ImmutableList<LLVMParameterAttribute> returnAttributes;

    /**
     * The signature of the called function (optional, maybe null).
     */
    private final ImmutableList<LLVMType> signature;

    /**
     * Flag indicating that the callee function does not access any allocas or varargs in the caller.
     * Not useful for us yet.
     */
    private final boolean tail;

    /**
     * Flag indicating whether the signature contains variably many types.
     */
    private final boolean varSizeSig;

    /**
     * @param id The variable to assign the result of the call to (null for 'void' functions).
     * @param conv The calling conventions.
     * @param fAttr The attributes of the function to call.
     * @param retAttr The attributes of the return value.
     * @param fName The name of the function to call.
     * @param sig The signature (optional, null if not specified).
     * @param moreTypes Is the signature of variable length?
     * @param params The parameters of the function to call.
     * @param tailMarker Flag indicating that the callee function does not access any allocas or varargs in the caller.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMCallInstruction(
        LLVMVariableLiteral id,
        LLVMCallingConvention conv,
        ImmutableList<LLVMFunctionAttribute> fAttr,
        ImmutableList<LLVMParameterAttribute> retAttr,
        LLVMVariableLiteral fName,
        ImmutableList<LLVMType> sig,
        boolean moreTypes,
        ImmutableList<ImmutablePair<LLVMFnParameter, LLVMLiteral>> params,
        boolean tailMarker,
        int debugLine
    ) {
        super(id, debugLine);
        this.callConv = conv;
        this.functionAttributes = fAttr;
        this.functionName = fName;
        this.functionParameters = params;
        this.tail = tailMarker;
        this.varSizeSig = moreTypes;
        this.signature = sig;
        this.returnAttributes = retAttr;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        vars.add(this.functionName.getName());
        for (ImmutablePair<LLVMFnParameter, LLVMLiteral> arg : this.functionParameters) {
            LLVMInstruction.collectVariable(vars, arg.y);
        }
        LLVMInstruction.collectVariable(vars, this.getIdentifier());
    }

    @Override
    public void collectUsedVariables(Collection<String> vars) {
        vars.add(this.functionName.getName());
        for (ImmutablePair<LLVMFnParameter, LLVMLiteral> arg : this.functionParameters) {
            LLVMInstruction.collectVariable(vars, arg.y);
        }
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
        // TODO too complicated for us now
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws
        AssertionException,
        ErrorStateException,
        UndefinedBehaviorException,
        MemorySafetyException,
        InvalidFreeException
    {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMType type = this.functionName.getType();
        final boolean useBoundedIntegers = state.getStrategyParamters().useBoundedIntegers;
        if (
            (LLVMDebuggingFlags.SV_COMP_MODE || LLVMDebuggingFlags.TERMCOMP_MODE)
            && this.functionName.getName().equals("@__VERIFIER_nondet_String")
            && this.functionParameters.isEmpty()
        ) {
            // special treatment for @__VERIFIER_nondet_String() in SV_COMP_MODE
            LLVMSymbolicVariable ref = termFactory.freshVariable();
            LLVMSymbolicVariable refToZero = termFactory.freshVariable();

            Set<LLVMRelation> newRels = new LinkedHashSet<>();

            LLVMAbstractState newState = state.incrementPC();
            newState = newState.allocateMemoryAndAssociatePointer(
                                                                  ref,
                                                                  refToZero,
                                                                  null,
                                                                  null,
                                                                  false,
                                                                  newRels,
                                                                  aborter
                    );
            newState = newState.setProgramVariable(
                                                   this.getIdentifier().getName(),
                                                   ref,
                                                   type
                    );
            newState = newState.setSimpleHeapEntry(
                                                   refToZero,
                                                   LLVMIntType.I8,
                                                   false,
                                                   termFactory.zero(),
                                                   aborter
                    );

            LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(newState, newRels);
            return Collections.singleton(evaluationResult);
        } else if (
            LLVMDebuggingFlags.SV_COMP_MODE
            && LLVMDebuggingFlags.USE_ASSERTION_EXCEPTIONS
            && this.functionName.getName().equals("@__VERIFIER_assert")
            && this.functionParameters.size() == 1
            && this.functionParameters.get(0).x.getType().isIntType()
        ) {
            // special treatment for @__VERIFIER_assert(i32 %i) in SV_COMP_MODE
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(
                    relationFactory.equalTo(
                        state.getSimpleTermForLiteral(this.functionParameters.get(0).y),
                        termFactory.one()
                    ),
                    aborter
                );
            if (check.x) {
                // assertion is true - function call is no-op
                return LLVMCallInstruction.noop(check.y);
            } else {
                // assertion could not be proven
                throw new AssertionException(nodeNumber);
            }
        } else if (
            LLVMDebuggingFlags.SV_COMP_MODE
            && LLVMDebuggingFlags.USE_ERROR_LOCATIONS
            && this.functionName.getName().equals("@__VERIFIER_error")
        ) {
            // special treatment for @__VERIFIER_error() in SV_COMP_MODE
            throw new ErrorStateException(nodeNumber);
        } else if (
            LLVMDebuggingFlags.SV_COMP_MODE
            && !LLVMDebuggingFlags.USE_ERROR_LOCATIONS
            && this.functionName.getName().equals("@__VERIFIER_error")
        ) {
            // special treatment for @__VERIFIER_error() in SV_COMP_MODE
            LLVMErrorState errorState =
                new LLVMErrorState(
                    state.getModule(),
                    state.getProgramPosition(),
                    state.getStrategyParamters(),
                    aborter
                );
            return Collections.singleton(new LLVMSymbolicEvaluationResult(errorState, Collections.emptySet()));
        } else if (
            LLVMDebuggingFlags.SV_COMP_MODE
            && this.functionName.getName().endsWith("nondet_uint")
            && this.functionParameters.isEmpty()
        ) {
            // special treatment for @__VERIFIER_nondet_uint() in SV_COMP_MODE
            final LLVMSymbolicVariable ref = termFactory.freshVariable();
            type = this.functionName.getType();
            final LLVMRelation rel = relationFactory.nonNegative(ref);
            return
                Collections.singleton(
                    new LLVMSymbolicEvaluationResult(
                        state.incrementPC().setProgramVariable(
                            this.getIdentifier().getName(),
                            ref,
                            type
                        ).addRelation(
                            rel,
                            aborter
                        ),
                        Collections.singleton(rel)
                    )
                );
        } else if (isMallocCall()) {
            return this.handleMalloc(state, nodeNumber, (LLVMPointerType)type, proveMemorySafety, aborter);
        } else if (isFreeCall()) {
            return handleFree(state, nodeNumber, termFactory, memoryTracker, aborter);
        } else if (
            !(state.getModule().getFunctions().get(this.functionName.getNameWithoutScope()) instanceof LLVMFnDefinition)
            && (
                this.getReturnType().isIntType()
                || this.getReturnType().isPointerType()
                || this.getReturnType() instanceof LLVMVoidType
                || this.getReturnType() instanceof LLVMFloatType
            )
        ) {
            if (this.getReturnType() instanceof LLVMVoidType) {
                // We interpret declared void functions as no-ops.
                return LLVMCallInstruction.noop(state);
            }
            /*
             * We interpret declared non-void functions such that these just return their (possibly
             * non-deterministically) computed value without modifying anything visible to the caller or
             * unwinding an exception.
             */
            LLVMSymbolicVariable ref = termFactory.freshVariable();
            type = this.functionName.getType();
            return
                Collections.singleton(
                    new LLVMSymbolicEvaluationResult(
                        state.incrementPC().setProgramVariable(this.getIdentifier().getName(), ref, type),
                        Collections.emptySet()
                    )
                );
        } else {
            List<LLVMLiteral> callParams = new ArrayList<LLVMLiteral>();
            for (ImmutablePair<LLVMFnParameter, LLVMLiteral> pair : this.functionParameters) {
                callParams.add(pair.y);
            }

            Set<LLVMRelation> newRels = new LinkedHashSet<>();
            LLVMAbstractState newState = state.pushCallStack(this.functionName.getNameWithoutScope(), callParams, newRels, aborter);

            LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(newState, newRels);
            return Collections.singleton(evaluationResult);
        }
    }

    private Set<LLVMSymbolicEvaluationResult> handleFree(LLVMAbstractState state, int nodeNumber,
            final LLVMTermFactory termFactory, LLVMMemoryChangeTracker memoryTracker, Abortion aborter) throws InvalidFreeException {
        if (isGuaranteedToBeFreeOfNullPointer(state, termFactory)) {
            return LLVMCallInstruction.noop(state);
        }
        Set<? extends LLVMRelation> rels = Collections.emptySet();
        LLVMLiteral startCell = this.functionParameters.get(0).y;
        LLVMSimpleTerm startRef = state.getSimpleTermForLiteral(startCell);
        if (startRef instanceof LLVMSymbolicVariable && state.isInitialStructPointer((LLVMSymbolicVariable)startRef)) {
            LLVMSymbolicEvaluationResult res = state.findAndCreateStructInvariantForNext((LLVMSymbolicVariable)startRef, aborter);
            state = res.x;
            rels = res.y;
        }
        // Find index for allocated area
        Pair<Integer,LLVMAbstractState> indexResult = getIndexOfFreedAllocation(state, nodeNumber, aborter);
        state = indexResult.y;
        if(indexResult.x < 0 && indexResult.y.getStrategyParamters().proveMemorySafety)
            throw new InvalidFreeException(nodeNumber);

        if(memoryTracker != null && indexResult.x >= 0) {
            LLVMAllocation allocationToFree = state.getAllocations().get(indexResult.x);
            memoryTracker.freedAllocationWhenEvaluatingState(state, allocationToFree);
        }

        return Collections.singleton(new LLVMSymbolicEvaluationResult(
                state.freeAllocation(indexResult.x, nodeNumber, aborter).incrementPC(), rels));
    }

    /**
     *
     * @param state
     * @param nodeNumber
     * @return The index of the allocation this @free call will release, or -1 if no such allocation exists
     * @throws InvalidFreeException
     */
    public Pair<Integer,LLVMAbstractState> getIndexOfFreedAllocation(LLVMAbstractState state, int nodeNumber, Abortion aborter)  {
        if(!isFreeCall())
            throw new IllegalStateException("Only call this method if this call is to the method @free");

        LLVMLiteral startCell = this.functionParameters.get(0).y;
        LLVMSimpleTerm startRef = state.getSimpleTermForLiteral(startCell);
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();

        //Quick check only using equality first
        int index = 0;
        for (LLVMAllocation allocation : state.getAllocations()) {
            if (allocation.x.equals(startRef)) {
                return new Pair<>(index,state);
            }
            index++;
        }

        //Now check respecting possible equalities
        index = 0;
        for (LLVMAllocation allocation : state.getAllocations()) {
            Pair<Boolean, ? extends LLVMAbstractState> check = state.checkRelation(
                    relationFactory.equalTo(allocation.x, startRef),
                    aborter
                );
            if(check.x) {
                return new Pair<>(index,check.y);
            }
            index++;
        }

        // Not found - then the call of free is invalid.
        return new Pair<>(-1,state);
    }

    /**
     *
     * @return True if we know that the address to free equals zero. False if not or we don't know
     */
    public boolean isGuaranteedToBeFreeOfNullPointer(LLVMAbstractState state, final LLVMTermFactory termFactory) {
        if(!isFreeCall())
            throw new IllegalStateException("Only call this method if this call is to the method @free");

        LLVMLiteral startCell = this.functionParameters.get(0).y;
        LLVMSimpleTerm startRef = state.getSimpleTermForLiteral(startCell);
        return startRef.equals(termFactory.zero());


    }

    public boolean isFreeCall() {
        return this.functionName.getName().equals("@free") && this.functionParameters.size() == 1;
    }

    public boolean isMallocCall() {
        return this.functionName.getName().equals("@malloc") && this.functionParameters.size() == 1;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        if (this.getIdentifier() != null) {
            res.append(eu.tttext(this.getIdentifier().toString()));
            res.append(eu.tttext(" = "));
        }
        if (this.tail) {
            res.append(eu.tttext("tail "));
        }
        res.append(eu.tttext("call"));
        if (this.callConv != null) {
            res.append(eu.tttext(" "));
            res.append(eu.tttext(this.callConv.toString()));
        }
        for (LLVMParameterAttribute attr : this.returnAttributes) {
            res.append(eu.tttext(" "));
            res.append(eu.tttext(attr.toString()));
        }
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.functionName.getType().toString()));
        if (this.signature != null) {
            res.append(eu.tttext(" ("));
            if (!this.signature.isEmpty()) {
                boolean first = true;
                for (LLVMType ty : this.signature) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(eu.tttext(","));
                    }
                    res.append(eu.tttext(ty.toString()));
                }
                if (this.varSizeSig) {
                    res.append(eu.tttext(",..."));
                }
            } else if (this.varSizeSig) {
                res.append(eu.tttext("..."));
            }
            res.append(eu.tttext(")*"));
        }
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.functionName.toString()));
        res.append(eu.tttext("("));
        if (this.functionParameters != null) {
            boolean first = true;
            for (ImmutablePair<LLVMFnParameter, LLVMLiteral> param : this.functionParameters) {
                if (first) {
                    first = false;
                } else {
                    res.append(eu.tttext(", "));
                }
                res.append(eu.tttext(param.x.toString()));
                res.append(eu.tttext(" "));
                res.append(eu.tttext(param.y.toString()));
            }
        }
        res.append(eu.tttext(")"));
        if (this.functionAttributes != null) {
            for (LLVMFunctionAttribute attr : this.functionAttributes) {
                res.append(eu.tttext(" "));
                res.append(eu.tttext(attr.toString()));
            }
        }
        return res.toString();
    }

    /**
     * @return The calling conventions.
     */
    public LLVMCallingConvention getCallConv() {
        return this.callConv;
    }

    /**
     * @return The attributes of the function to call.
     */
    public ImmutableList<LLVMFunctionAttribute> getFunctionAttributes() {
        return this.functionAttributes;
    }

    /**
     * @return The name of the function to call;
     */
    public LLVMVariableLiteral getFunctionName() {
        return this.functionName;
    }

    /**
     * @return The parameters of the function to call.
     */
    public ImmutableList<ImmutablePair<LLVMFnParameter, LLVMLiteral>> getFunctionParameters() {
        return this.functionParameters;
    }

    @Override
    public Set<String> getInterestingVariables() {
        return Collections.emptySet();
    }

    /**
     * @return The attributes of the return value.
     */
    public ImmutableList<LLVMParameterAttribute> getReturnAttributes() {
        return this.returnAttributes;
    }

    /**
     * @return The return type of the function to call.
     */
    public LLVMType getReturnType() {
        return this.functionName.getType();
    }

    /**
     * @return The signature (maybe null).
     */
    public ImmutableList<LLVMType> getSignature() {
        return this.signature;
    }

    /**
     * @return True if the callee function does not access any allocas or varargs in the caller. False otherwise.
     */
    public boolean isTail() {
        return this.tail;
    }

    /**
     * @return True if he signature may contain more types than specified.
     */
    public boolean isVarSizeSig() {
        return this.varSizeSig;
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        // no overapproximation, if we have void functions or __VERIFIER_nondet_* in SV-COMP mode
        if (
            ((LLVMDebuggingFlags.SV_COMP_MODE || LLVMDebuggingFlags.TERMCOMP_MODE)
            && (this.functionName.getName().startsWith("@__VERIFIER_nondet_") || this.functionName.getName().startsWith("@nondet"))
            && this.functionParameters.isEmpty())
            || this.getReturnType() instanceof LLVMVoidType
        ) {
            return false;
        }
        // no overapproximation, if we have declared function without a definition
        if (!(state.getModule().getFunctions().get(this.functionName.getNameWithoutScope()) instanceof LLVMFnDefinition)) {
            return false;
        }
        int instructionCount = state.getModule().getAllPositions().size();
        if(instructionCount > Globals.INSTRUCTION_COUNT_THRESHOLD) {
            return false;
        }
        return true;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("CallInstr ");
        strBuilder.append(" tail: " + this.tail);
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" callConv: " + this.callConv);
        strBuilder.append(" returnType: " + this.functionName.getType());
        strBuilder.append(" fnName: " + this.functionName);
        boolean first = true;
        strBuilder.append(" parameters: (");
        for (ImmutablePair<LLVMFnParameter, LLVMLiteral> pair : this.functionParameters) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + "(type: " + pair.x + ", value: " + pair.y + ")");
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
            strBuilder.append(" " + fnAttribute);
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
     * Executes the necessary instructions for evaluate if malloc is called.
     * @param state The state to evaluate.
     * @param nodeNumber For debugging purposes.
     * @param type The return type of malloc.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return A pair, containing the result of evaluation and an empty set of relations describing that there is no
     *         changes between the input and output state.
     * @throws UndefinedBehaviorException If it cannot be proven that the evaluation of this instruction is
     *                                    sufficiently defined.
     */
    private Set<LLVMSymbolicEvaluationResult> handleMalloc(
        LLVMAbstractState state,
        int nodeNumber,
        LLVMPointerType type,
        boolean proveMemorySafety,
        Abortion aborter
    ) throws UndefinedBehaviorException {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final Set<LLVMRelation> newRels = new LinkedHashSet<>();
        // Heap memory allocation
        // determine the new variable (malloc returns *i8)
        // TODO: malloc may return 0
        LLVMSymbolicVariable newRef = termFactory.freshVariable();
        LLVMSimpleTerm arg = state.getSimpleTermForLiteral(this.functionParameters.get(0).y);
        int align = 0;
        LLVMAbstractState newState = state;
        if (arg instanceof LLVMConstant) {
            BigInteger offset = ((LLVMConstant)arg).getIntegerValue().subtract(BigInteger.ONE);
            if (offset.compareTo(BigInteger.ZERO) == 0) {
                // Constant sized allocation of one memory cell
                newState = newState.allocateMemoryAndAssociatePointer(newRef, newRef, null, null, false, newRels, aborter);
            } else if (offset.compareTo(BigInteger.ZERO) < 0) {
                throw
                    new UndefinedBehaviorException(
                        "Allocation of zero or negative number of bytes at node " + nodeNumber + "."
                    );
            } else {
                // Constant sized allocation of more than one memory cell
                LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                LLVMRelation rel = relationFactory.createAdditionRelation(limitRef, newRef, termFactory.constant(offset));
                if (newRels != null) {
                    newRels.add(rel);
                }
                newState = newState.addRelation(rel, aborter);
                newState = newState.allocateMemoryAndAssociatePointer(
                               newRef,
                               limitRef,
                               null,
                               null,
                               false,
                               newRels,
                               aborter
                           );
            }
            if (offset.compareTo(BigInteger.valueOf(3)) >= 0) {
                align = 4;
            }
            newState = LLVMAllocaInstruction.upperBound(newState, newRef, type, offset, newRels, aborter);
        } else {
            // we have a variable size allocation
            LLVMSymbolicVariable numRef = (LLVMSymbolicVariable)arg;
            if (newState.isPossiblyTrapValue(numRef)) {
                throw new TrapValueException(nodeNumber);
            }
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                newState.checkRelation(relationFactory.positive(numRef), aborter);
            newState = check.y;
            if (proveMemorySafety && !check.x) {
                throw new UndefinedBehaviorException(
                    "Allocation parameter might be zero or negative at node " + nodeNumber + "!"
                );
            }
            LLVMSymbolicVariable limitRef = termFactory.freshVariable();

            newState = newState.applyArrayPatternHeuristicForAllocation(
                            newRef,
                            numRef,
                            limitRef
                        );

            LLVMRelation rel = relationFactory.equalTo(
                                   termFactory.operation(
                                       ArithmeticOperationType.ADD,
                                       newRef,
                                       numRef
                                   ),
                                   termFactory.operation(
                                       ArithmeticOperationType.ADD,
                                       termFactory.one(),
                                       limitRef
                                   )
                               );

            newState = newState.addRelation(rel, aborter);
            newState = newState.allocateMemoryAndAssociatePointer(
                            newRef,
                            limitRef,
                            null,
                            null,
                            false,
                            newRels,
                            aborter
                        );
        }
        // create modulo relation for alignment
        if (align > 1) {
            if (Globals.useAssertions) {
                // clang requires this; llvm specification seems not to be specific about it.
                assert (IntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
            }

            LLVMRelation alignmentRel = relationFactory.createAlignmentRelation(newRef, termFactory.constant(BigInteger.valueOf(align)));
            newRels.add(alignmentRel);
            newState = newState.addRelation(alignmentRel, aborter);
        }
        // Set entry in variable function and increment program counter
        return
            Collections.singleton(
                new LLVMSymbolicEvaluationResult(
                    newState.setProgramVariable(this.getIdentifier().getName(), newRef, type).incrementPC(),
                    newRels
                )
            );
    }

    /**
     * @param dot Should the String comply to the DOT format?
     * @return A String representation for this object.
     */
    private String toString(boolean dot) {
        StringBuilder res = new StringBuilder();
        if (this.getIdentifier() != null) {
            res.append(dot ? this.getIdentifier().toDOTString() : this.getIdentifier().toString());
        } else {
            res.append("Unnamed Call-Instruction");
        }
        res.append(" = ");
        if (this.tail) {
            res.append("tail ");
        }
        res.append("call");
        if (this.callConv != null) {
            res.append(" ");
            res.append(this.callConv);
        }
        for (LLVMParameterAttribute attr : this.returnAttributes) {
            res.append(" ");
            res.append(attr);
        }
        res.append(" ");
        res.append(this.functionName.getType());
        if (this.signature != null) {
            res.append(" (");
            if (!this.signature.isEmpty()) {
                boolean first = true;
                for (LLVMType ty : this.signature) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(",");
                    }
                    res.append(ty.toString());
                }
                if (this.varSizeSig) {
                    res.append(",...");
                }
            } else if (this.varSizeSig) {
                res.append("...");
            }
            res.append(")*");
        }
        res.append(" ");
        res.append(this.functionName);
        res.append("(");
        if (this.functionParameters != null) {
            boolean first = true;
            for (ImmutablePair<LLVMFnParameter, LLVMLiteral> param : this.functionParameters) {
                if (first) {
                    first = false;
                } else {
                    res.append(", ");
                }
                res.append(param.x);
                res.append(" ");
                res.append(param.y);
            }
        }
        res.append(")");
        if (this.functionAttributes != null) {
            for (LLVMFunctionAttribute attr : this.functionAttributes) {
                res.append(" ");
                res.append(attr);
            }
        }
        return res.toString();
    }

    @Override
    public String toLLVMIR() {
        return toString();
    }

}
