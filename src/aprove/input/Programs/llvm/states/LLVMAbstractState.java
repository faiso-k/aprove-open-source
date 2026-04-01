package aprove.input.Programs.llvm.states;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import org.json.JSONObject;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.literals.const_expr.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * An abstract state is the representation of all information we have at a certain point during symbolic program
 * execution.
 * @author Janine Repke, Jera Hensel, cryingshadow
 */
public class LLVMAbstractState implements Immutable, DOTStringAble, JSONExport {

    private final int hashCode = 4639;
    
    /**
     * The count of the initial state.
     */
    public static final int PC_START = 0;

    /**
     * Updates the state in the first evaluation result to the state of the second one and adds all relations from the
     * second evaluation result to the first one.
     * @param res Some evaluation result.
     * @param post The result of the post-processing of the state in the specified evaluation result.
     */
    private static void updateEvaluationResult(
        LLVMSymbolicEvaluationResult res,
        LLVMSymbolicEvaluationResult post
    ) {
        res.x = post.x;
        Set<LLVMRelation> set = new LinkedHashSet<LLVMRelation>(res.y);
        set.addAll(post.y);
        res.y = set;
    }
    
    /**
     * This is only used if this state is part of a function graph, i.e., it is analyzed using summarization technqiues.
     * Otherwise, this is null.
     * 
     * If the map is used it maps variables in the entry state to equivalent variables in this state 
     */
    private final ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> entryStateVarCorrespondenceMap;
    
    /**
     * Used for modularization/intersecting. For an index i in the allocation list of this state, may contain
     * an boolean which indicates whether the allocation was possibly modified since the entry state.
     */
    private final ImmutableMap<Integer,Boolean> allocationChangedSinceEntryState;

    /**
     * Stores the indices of the allocated memory areas which have been allocated by some malloc instruction.
     * The allocated areas must be freed by a corresponding call of free.
     */
    private final ImmutableTreeSet<Integer> allocatedByMalloc;

    /**
     * Stores the indices of the allocated memory areas which have been allocated by some alloca instruction within the
     * current function. The allocated areas are freed automatically when the function returns.
     */
    private final ImmutableTreeSet<Integer> allocatedInCurrentFunctionFrame;

    /**
     * The call stack.
     */
    private final ImmutableDeque<LLVMReturnInformation> callStack;


    /**
     * Contains knowledge of integer relations over references.
     */
    private final LLVMIntegerState integerState;

    /**
    * Flag indicating that this state is the result of a call stack abstraction (omitting all but the topmost
    * stackframe).
    */
    private final boolean isAbstractRecursiveFunctionStart;

    /**
     * The LLVM program.
     */
    private final LLVMModule module;

    /**
     * Map from references being possible trap values to pairs of references and offsets whose provable association to
     * some allocated memory area would imply that the former references are no trap values.
     */
    private final ImmutableMap<LLVMSymbolicVariable, LLVMTrapCondition> possibleTrapValues;

    /**
     * The program position triple containing the name of the function currently in execution, the name of the basic
     * block currently in execution, and the number of the instruction (program counter, 0 is first position) within
     * this basic block.
     */
    private final LLVMProgramPosition programPosition;

    /**
     * Contains all variables of this state.
     */
    private final ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> programVariables;

    /**
     * True iff this state is a refinement of another state.
     */
    private final boolean refined;

    /**
     * The cached relation factory specified in the strategy parameters.
     */
    private final transient LLVMRelationFactory relFact;

    /**
     * Strategy parameters.
     */
    private final LLVMParameters strategyParameters;
    
    
    /**
     * We store the symbolic variables of this state here as soon as we have calculated them once (discarded when constructing new state)
     */
    private ImmutableSet<LLVMSymbolicVariable> symbolicVariableCache;

    
    private Map<LLVMSymbolicVariable, ImmutableSet<LLVMSymbolicVariable>> symbolicVariableEquivalenceClassCache;
    
    /**
     * Creates a fully initialized program state using the specified set of relations directly.
     * @param newModule The llvm module.
     * @param newVariables The variable function.
     * @param newFunctionAllocations The indices of memory areas allocated within the current function's frame.
     * @param newProgPos The program position triple containing the name of the function currently in execution, the
     *                   name of the basic block currently in execution, and the number of the instruction (program
     *                   counter, 0 is first position) within this basic block.
     * @param newCallStack The call stack.
     * @param isRefined The refinement flag.
     * @param integerState The integer knowledge.
     * @param isAbstractRecursiveFunctionStart TODO
     * @param newAllocatedByMalloc The indices of allocations which have been allocated by malloc.
     * @param traps Possible trap values.
     * @param params Strategy parameters.
     * @param varToEntryStateVars Map of variables in entry state to corresponding variables in this state. only non-null for states part of functions we want to intersect  
     */
    protected LLVMAbstractState(
        LLVMModule newModule,
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVariables,
        ImmutableTreeSet<Integer> newFunctionAllocations,
        LLVMProgramPosition newProgPos,
        ImmutableDeque<LLVMReturnInformation> newCallStack,
        boolean isRefined,
        LLVMIntegerState integerState,
        boolean isAbstractRecursiveFunctionStart,
        ImmutableTreeSet<Integer> newAllocatedByMalloc,
        ImmutableMap<LLVMSymbolicVariable, LLVMTrapCondition> traps,
        LLVMParameters params, 
        ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> entryStateVarCorrespondenceMap,
        ImmutableMap<Integer,Boolean> allocationChangedSinceEntryState
    ) {
        this.module = newModule;
        this.programVariables = newVariables;
        this.callStack = newCallStack;
        this.allocatedInCurrentFunctionFrame = newFunctionAllocations;
        this.programPosition = newProgPos;
        this.refined = isRefined;
        this.integerState = integerState;
        this.isAbstractRecursiveFunctionStart = isAbstractRecursiveFunctionStart;
        this.allocatedByMalloc = newAllocatedByMalloc;
        this.possibleTrapValues = traps;
        this.strategyParameters = params;
        this.relFact = params.SMTsolver.stateFactory.getRelationFactory();
        this.entryStateVarCorrespondenceMap = entryStateVarCorrespondenceMap;
        this.allocationChangedSinceEntryState = allocationChangedSinceEntryState;
    }

    /**
     * @param rel Some relation.
     * @return A state where the knowledge encoded by the specified relation has been added.
     */
    public LLVMAbstractState addRelation(LLVMRelation rel, Abortion aborter) {
        return this.setIntegerState(this.getIntegerState().addRelation(rel, aborter));
    }

    /**
     * This method must not be called with references violating the mutual exclusion of allocated memory areas!
     * @param lower The lower bound of the allocated memory area.
     * @param upper The upper bound of the allocated memory area.
     * @param pointer The pointer belonging to the allocated memory area (may be null, then no additional pointer is
     *                associated).
     * @param type The type of the pointer (must be null iff pointer is null).
     * @param withinFunctionFrame Is the allocation performed within the current function frame (true) or on the heap
     *                            (false)?
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return An abstract state with a new allocated memory area between lower and upper as the last allocation (i.e.,
     *         its index is allocations.size() - 1), pointer being associated to this new area if it is not null, and
     *         everything else as in the current state.
     */
    public LLVMAbstractState allocateMemoryAndAssociatePointer(
        LLVMSymbolicVariable lower,
        LLVMSymbolicVariable upper,
        LLVMSymbolicVariable pointer,
        LLVMPointerType type,
        boolean withinFunctionFrame,
        Set<LLVMRelation> newRels, 
        Abortion aborter
    ) {
        if (Globals.useAssertions) {
            assert ((pointer == null) == (type == null)) : "Type must be null iff pointer is null!";
            for (LLVMAllocation memory : this.getAllocations()) {
                assert (!memory.x.equals(lower)) : "Double allocation!";
                assert (!memory.y.equals(lower)) : "Double allocation!";
                assert (!memory.x.equals(upper)) : "Double allocation!";
                assert (!memory.y.equals(upper)) : "Double allocation!";
                assert (!memory.x.equals(pointer)) : "Illegal association!";
                assert (!memory.y.equals(pointer)) : "Illegal association!";
            }
        }
        List<LLVMAllocation> newAllocMem = new ArrayList<LLVMAllocation>(this.getAllocations());
        newAllocMem.add(new LLVMAllocation(lower, upper));
        Integer allocIndex = newAllocMem.size() - 1;
        LLVMAbstractState res = this;
        if (withinFunctionFrame) {
            TreeSet<Integer> newFunctionFrameAllocs = new TreeSet<Integer>(this.getAllocatedInCurrentFunctionFrameIndices());
            newFunctionFrameAllocs.add(allocIndex);
            res = res.setAllocatedMemoryForAlloca(newAllocMem, newFunctionFrameAllocs);
        } else {
            TreeSet<Integer> newHeapAllocs = new TreeSet<Integer>(this.getAllocatedByMallocIndices());
            newHeapAllocs.add(allocIndex);
            res = res.setAllocatedMemoryForMalloc(newAllocMem, newHeapAllocs);
        }
        if (pointer != null) {
            res = res.associateAccess(pointer, type, allocIndex, newRels, aborter);
        }
        return res;
    }

    /**
     * @param newVar The variable for the pointer to the allocation.
     * @param numVar The variable for the size of the allocation.
     * @param limitVar The variable for the end of the allocation.
     * @return This state where an array pattern heuristic has been applied if applicable.
     */
    public LLVMAbstractState applyArrayPatternHeuristicForAllocation(
        LLVMSymbolicVariable newVar,
        LLVMSymbolicVariable numVar,
        LLVMSymbolicVariable limitVar
    ) {
        return this;
    }

    /**
     * @param var The program variable to assign a value to.
     * @param value The value to be assigned to the variable.
     * @param valueType The value type.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return A state where the specified value has been assigned to the specified program variable.
     */
    public LLVMAbstractState assign(String var, LLVMTerm value, LLVMType valueType, Set<LLVMRelation> newRels, Abortion aborter) {
        final LLVMSymbolicVariable freshVar = this.getRelationFactory().getTermFactory().freshVariable();
        LLVMAbstractState res = this.setProgramVariable(var, freshVar, valueType);
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        if (this.getStrategyParamters().useBoundedIntegers) {
            // TODO consider unsigned variables
            boolean unsigned = this.getModule().getUnsignedBitvectorVariables().contains(var);
            final IntegerType integerType = valueType.getIntegerType(unsigned, true);
            final LLVMRelation lowerBoundRel = relationFactory.lessThanEquals(termFactory.constant(integerType.getLower().getConstant()), freshVar);
            final LLVMRelation upperBoundRel = relationFactory.lessThanEquals(freshVar, termFactory.constant(integerType.getUpper().getConstant()));
            res = res.addRelation(lowerBoundRel, aborter).addRelation(upperBoundRel, aborter);
            if (newRels != null) {
                newRels.add(lowerBoundRel);
                newRels.add(upperBoundRel);
            }
        }
        if (value != null) {
            final LLVMRelation assignRel = relationFactory.equalTo(freshVar, value);
            res = res.addRelation(assignRel, aborter);
            if (newRels != null) {
                newRels.add(assignRel);
            }
        }
        return res;
    }

    /**
     * @param pointer The pointer to associate.
     * @param type The type of the pointer.
     * @param index The index of the allocated memory area to associate <code>pointer</code> with.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return An abstract state with the specified pointer association and everything else as in the current state.
     */
    public LLVMAbstractState associateAccess(LLVMSymbolicVariable pointer, LLVMPointerType type, Integer index, Set<LLVMRelation> newRels, Abortion aborter) {
        return
            this.setIntegerState(
                this.getIntegerState().associateAccess(pointer, type, index, newRels, aborter)
            );
    }

    /**
     * @param branchLabel The label of the block to branch to.
     * @param nodeNumber The current node number.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return An AbstractState with the last block changed to the current one, the current to the specified one, the
     *         program counter set to 0, and which is not refined. Everything else is as in the current state.
     * @throws UndefinedBehaviorException If we access a trap value.
     */
    public LLVMAbstractState branchToBlock(String branchLabel, int nodeNumber, Set<LLVMRelation> newRels, Abortion aborter) throws UndefinedBehaviorException {
        String lastExecutedBlock = this.getCurrentBlock();
        LLVMAbstractState res =
            this.setProgramPosition(new LLVMProgramPosition(this.getCurrentFunction(), branchLabel, 0));
        LLVMInstruction instruction = res.getCurrentInstruction();
        while (instruction instanceof LLVMPhiInstruction) {
            final LLVMPhiInstruction phi = (LLVMPhiInstruction)instruction;
            // find fitting block and so the fitting literal (compare with all given blocks)
            LLVMLiteral foundLit = null;
            for (ImmutablePair<String, LLVMLiteral> actArgument : phi.getArgumentPairs()) {
                if (actArgument.x.equals(lastExecutedBlock)) {
                    foundLit = actArgument.y;
                    break;
                }
            }
            if (Globals.useAssertions) {
                assert (foundLit != null) :
                    "There should always be a last block which fits to one of the given blocks in the phi instruction";
            }
            // set the new variable to this found value (note that the old state "this" must be taken for atomic
            // execution of several consecutive phi instructions)
            LLVMSimpleTerm term = this.getSimpleTermForLiteral(foundLit);
            if (this.isPossiblyTrapValue(term)) {
                throw new TrapValueException(nodeNumber);
            }
            res = res.assign(phi.getIdentifier().getName(), term, phi.getValueType(), newRels, aborter).incrementPC();
            instruction = res.getCurrentInstruction();
        }
        return res;
    }

    /**
     * @param term The term to be checked.
     * @return True if this state implies that the term is non-negative. False otherwise.
     */
    public Pair<Boolean, ? extends LLVMAbstractState> checkIfNonNegative(
        LLVMTerm term,
        Abortion aborter
    ) {
        LLVMTermFactory termFactory = getRelationFactory().getTermFactory();
        return this.checkRelation(term, IntegerRelationType.GE, termFactory.constant(0), aborter);
    }

    /**
     * @param term The term to be checked.
     * @return True if this state implies that the term is positive. False otherwise.
     */
    public Pair<Boolean, ? extends LLVMAbstractState> checkIfPositive(
        LLVMTerm term,
        Abortion aborter
    ) {
        LLVMTermFactory termFactory = getRelationFactory().getTermFactory();
        return this.checkRelation(term, IntegerRelationType.GT, termFactory.constant(0), aborter);
    }

    /**
     * @param rel Some relation.
     * @return True if this state implies that the specified relation holds. False otherwise.
     */
    public Pair<Boolean, ? extends LLVMAbstractState> checkRelation(IntegerRelation rel, Abortion aborter) {
        final Pair<Boolean, ? extends LLVMIntegerState> res =
            this.getIntegerState().checkRelation(rel, aborter);
        return new Pair<Boolean, LLVMAbstractState>(res.x, this.setIntegerState(res.y));
    }

    /**
     * @param lhs The left-hand side of the relation.
     * @param type The relation type.
     * @param rhs The right-hand side of the relation.
     * @return True if this state implies that the specified relation holds. False otherwise.
     */
    public Pair<Boolean, ? extends LLVMAbstractState> checkRelation(
        LLVMTerm lhs,
        IntegerRelationType type,
        LLVMTerm rhs, 
        Abortion aborter
    ) {
        return this.checkRelation(this.getRelationFactory().createRelation(type, lhs, rhs), aborter);
    }

    /**
     * @return An AbstractState at the same program position and with the same call stack and refinement status as in
     *         the current state. Everything else is cleared.
     */
    public LLVMAbstractState clearKnowledge(Abortion aborter) {
        final FrontendSMT smt = this.getStrategyParamters().SMTsolver;
        return
            new LLVMAbstractState(
                this.getModule(),
                ImmutableCreator.create(Collections.emptyMap()),
                ImmutableCreator.create(new TreeSet<Integer>()),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                new LLVMDefaultIntegerState(
                    new PlainIntegerRelationState(smt.smtSolverFactory, smt.smtLogic),
                    ImmutableCreator.create(Collections.emptyList()),
                    ImmutableCreator.create(Collections.emptyMap()),
                    ImmutableCreator.create(Collections.emptyMap()),
                    ImmutableCreator.create(Collections.emptySet()),
                    this.getStrategyParamters(), 
                    aborter
                ),
                false,
                ImmutableCreator.create(new TreeSet<Integer>()),
                ImmutableCreator.create(Collections.emptyMap()),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState == null ? null : ImmutableCreator.create(Collections.emptyMap())
            );
    }

    /**
     * Evaluate this state according to the next instruction.
     * @param nodeNumber For debugging purposes.
     * @param proveMemorySafety indicates whether we have to prove memory safety (may override setting from LLVMParameters!)
     * @param memoryTracker must be notified when evaluating free and store about what we did. May be null, then nothing is needed to do
     * @return The new state after evaluation of this state.
     * @throws MemorySafetyException If memory safety of the evaluation cannot be proven.
     * @throws UndefinedBehaviorException If it cannot be proven that the evaluation is sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions within the LLVM program cannot be proven during
     *                            evaluation.
     * @throws ErrorStateException If an error state is reached.
     */
    public Set<LLVMSymbolicEvaluationResult> evaluate(int nodeNumber, boolean proveMemorySafety, boolean removeNonLiveVariables, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws MemorySafetyException, UndefinedBehaviorException, AssertionException, ErrorStateException {
        LLVMInstruction actInstruction = this.getCurrentInstruction();
        if (this.isErrorState() || this.isInconsistentState() || this.getCurrentInstruction() instanceof LLVMUnreachableInstruction) {
            // an error state has no successors
            return null;
        }
        // TODO save instruction in this state?
        Set<LLVMSymbolicEvaluationResult> evaluations = actInstruction.evaluate(this, nodeNumber, proveMemorySafety, memoryTracker, aborter);
        if (evaluations.size() == 1) {
            LLVMSymbolicEvaluationResult evaluation = evaluations.iterator().next();
            LLVMSymbolicEvaluationResult post = evaluation.getState().postProcessAfterEvaluation(evaluation.y, removeNonLiveVariables, aborter);
            LLVMAbstractState.updateEvaluationResult(evaluation, post);
            return Collections.singleton(evaluation);
        } else {
            // A refinement took place while evaluating the expression
            Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
            for (LLVMSymbolicEvaluationResult refinement : evaluations) {
                if (!refinement.x.isInconsistentState()) {
                    LLVMSymbolicEvaluationResult post = refinement.getState().postProcessAfterRefinement(aborter, removeNonLiveVariables);
                    LLVMAbstractState.updateEvaluationResult(refinement, post);
                }
                res.add(refinement);
            }
            return res;
        }
    }

    public LLVMAbstractState findAndCreateInvariantsForAccess(LLVMMemoryRange storeAccess, Abortion aborter) {
        LLVMAbstractState res = this;
        Deque<LLVMMemoryRange> newRanges = new ArrayDeque<LLVMMemoryRange>();
        newRanges.push(storeAccess);
        while (!newRanges.isEmpty()) {
            LLVMMemoryRange range = newRanges.poll();
            newRanges.remove(range);
            LLVMMemoryInvariant stored_inv = res.getMemory().get(range);
            for (LLVMMemoryRange iter : res.getMemory().keySet()) {
                Pair<LLVMMemoryRange, LLVMAbstractState> mergedRange = LLVMMemoryRange.mergeLeft(res, iter, range, aborter);
                res = mergedRange.y;
                if (mergedRange.x == null) {
                    mergedRange = LLVMMemoryRange.mergeRight(res, iter, range, aborter);
                    res = mergedRange.y;
                }
                if (mergedRange.x != null && stored_inv != null) {
                    LLVMMemoryInvariant other_inv = res.getMemory().get(iter);
                    Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> mergedInv =
                        other_inv.joinInvariant(res, stored_inv, aborter);
                    res = mergedInv.y;
                    if (mergedInv.x != null && !res.getMemory().containsKey(mergedRange.x)) {
                        res = res.setHeapEntry(mergedRange.x, mergedInv.x);
                        newRanges.push(mergedRange.x);
                    }
                }
            }
        }
//        return res.cleanHeapInvariants(aborter);
        return res;
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariantForNext(LLVMSymbolicVariable startRef, Abortion aborter) {
        return new LLVMSymbolicEvaluationResult(this,new LinkedHashSet<LLVMRelation>());
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariantForNext(LLVMMemoryRange storeAccess, LLVMSymbolicVariable freshPointer, Abortion aborter) {
        return new LLVMSymbolicEvaluationResult(this,new LinkedHashSet<LLVMRelation>());
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariants(LLVMMemoryRange storeAccess, Abortion aborter) {
        return new LLVMSymbolicEvaluationResult(this,new LinkedHashSet<LLVMRelation>());
    }

    public Set<LLVMSymbolicEvaluationResult> findAndRefineStructInvariant(LLVMMemoryRange storeAccess, Abortion aborter) {
        return Collections.singleton(new LLVMSymbolicEvaluationResult(this,new LinkedHashSet<LLVMRelation>()));
    }

//    public LLVMAbstractState findFurtherInvariants(Collection<Relation> newRels, LLVMParameters params) {
//        LLVMAbstractState res = this;
//        for (Relation rel : newRels) {
//            res = res.findAndJoinFurtherInvariants(rel.getReferences(),params);
//        }
//        return res;
//    }

    /**
     * @return A copy of this state where the isAstractRecursiveFunctionStart flag is set to true.
     */
    public LLVMAbstractState flagAbstractRecursiveFunctionStart() {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                this.getIntegerState(),
                true,
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.getAllocationChangedSinceEntryStateMap()
            );
    }

    /**
     * @param index The index of the allocation to free.
     * @param nodeNumber The current node number.
     * @return This state where the specified allocation has been freed and heap entries therein have been removed.
     * @throws InvalidFreeException If the specified index does not belong to the allocations that have been
     *                              allocated by malloc.
     */
    public LLVMAbstractState freeAllocation(int index, int nodeNumber, Abortion aborter) throws InvalidFreeException {
        if (this.getAllocatedByMallocIndices().contains(index)) {
            return this.removeAllocation(index, true, aborter);
        }
        if (this.strategyParameters.proveMemorySafety) {
            throw new InvalidFreeException(nodeNumber);
        }
        return this;
    }
    
    
    /**
     * Like <code>freeAllocation</code>, but it does not remove heap entries within the freed allocation.
     * This is only necessary for the construction of intersections of recursive functions and should otherwise not be used.
     * @param index
     * @param nodeNumber
     * @param aborter
     * @return
     * @throws InvalidFreeException
     */
    public LLVMAbstractState freeAllocationWithoutRemovingHeapEntries(int index, int nodeNumber, Abortion aborter) throws InvalidFreeException {
        if (this.getAllocatedByMallocIndices().contains(index)) {
            return this.removeAllocation(index, false, aborter);
        }
        if (this.strategyParameters.proveMemorySafety) {
            throw new InvalidFreeException(nodeNumber);
        }
        return this;
    }

    /**
     * @return A generalized abstract LLVM state emerging from the current one without a merge partner. The symbolic
     *         variables must not be renamed to fresh names in that case. Null if no generalization is to be performed
     *         that way.
     */
    public LLVMAbstractState generalizeWithoutMerging() {
        return null;
    }

    /**
     * @return The indices of the allocated memory areas which have been allocated using malloc.
     */
    public ImmutableTreeSet<Integer> getAllocatedByMallocIndices() {
        return this.allocatedByMalloc;
    }
    
    /**
     * @return The allocated memory areas which have been allocated using malloc.
     */
    public Set<LLVMAllocation> getAllocatedByMalloc() {
    	Set<LLVMAllocation> allocatedByMallocAllocations = new LinkedHashSet<>();
    	for(int mallocIndex : allocatedByMalloc)
    		allocatedByMallocAllocations.add(getAllocations().get(mallocIndex));
    	return allocatedByMallocAllocations;
        //return allocatedByMalloc.stream().map(getAllocations()::get).collect(Collectors.toSet());

    }

    /**
     * @return The indices of the allocated memory areas which have been allocated within the current function.
     */
    public ImmutableTreeSet<Integer> getAllocatedInCurrentFunctionFrameIndices() {
        return this.allocatedInCurrentFunctionFrame;
    } 
    
    public ImmutableTreeSet<Integer> getAllStackAllocatedIndices() {
    	TreeSet<Integer> allStackAllocations = new TreeSet<>(this.getAllocatedInCurrentFunctionFrameIndices());
    	for(LLVMReturnInformation stackFrame : getCallStack()) {
    		allStackAllocations.addAll(stackFrame.getAllocationsInFunction());
    	}
        return ImmutableCreator.create(allStackAllocations);
    } 
    
    /**
     * @return The allocated memory areas which have been allocated within the current function.
     */
    public Set<LLVMAllocation> getAllocatedInCurrentFunctionFrame() {
    	Set<LLVMAllocation> allocatedInCurrentFunctionFrameAllocations = new LinkedHashSet<>();
    	for(int mallocIndex : allocatedInCurrentFunctionFrame)
    		allocatedInCurrentFunctionFrameAllocations.add(getAllocations().get(mallocIndex));
    	return allocatedInCurrentFunctionFrameAllocations;
    	//return allocatedInCurrentFunctionFrame.stream().map(getAllocations()::get).collect(Collectors.toSet());
    }

    /**
     * @return The allocated memory areas.
     */
    public ImmutableList<LLVMAllocation> getAllocations() {
        return this.getIntegerState().getAllocations();
    }

    /**
     * @param term Some simple term (variable or constant) which is a pointer.
     * @param type The type of the term.
     * @param oneMore Is one byte after the allocation ok? If false, the resulting boolean flag must also be false.
     * @return The index of the allocation to which the specified term is associated to, a flag whether the specified
     *         address is exactly one cell behind the allocation, and the abstract state after this check. The first
     *         component is null if there is no such allocation.
     */
    public Pair<LLVMAssociationIndex, LLVMAbstractState> getAssociatedAllocationIndex(
        LLVMTerm term,
        LLVMPointerType type,
        boolean oneMore,
        Abortion aborter
    ) {
        final Pair<LLVMAssociationIndex, ? extends LLVMIntegerState> res =
            this.getIntegerState().getAssociatedAllocationIndex(
                term,
                type,
                oneMore,
                aborter
            );
        return new Pair<LLVMAssociationIndex, LLVMAbstractState>(res.x, this.setIntegerState(res.y));
    }
    
	public Pair<LLVMAssociationIndex, LLVMAbstractState> getAssociatedAllocationIndex(LLVMMemoryRange range, Abortion aborter) {
		LLVMSimpleTerm from = range.getFromRef();

		final int pointerSize = this.getModule().getPointerSize();
		Pair<LLVMAssociationIndex, LLVMAbstractState> pairForLowerBound = getAssociatedAllocationIndex(
				getRelationFactory().getTermFactory().create(from),
				new LLVMPointerType(range.getType(), pointerSize, null), false, aborter);

		LLVMTermFactory termFactory = getRelationFactory().getTermFactory();
		final LLVMConstant offset = termFactory.constant(BigInteger.valueOf(IntegerUtils.bitsToBytes(range.getType().size()) - 1));
		LLVMTerm upperBound = termFactory.add(range.getToRef(), offset);

		if(pairForLowerBound == null || pairForLowerBound.x == null)
			return pairForLowerBound; //Didn't find anything
		
		//So far, we only got a potential allocation containing the lower bound, not necessarily the whole range
		if (range.isPointwise()) {
			return pairForLowerBound;
		} else {
			LLVMAllocation correspondingAllocation = getAllocations().get(pairForLowerBound.x.x);
			LLVMTerm upperBoundOfPotentialAllocation = correspondingAllocation.y;

			Pair<Boolean, ? extends LLVMAbstractState> check = pairForLowerBound.y.checkRelation(
					getRelationFactory().lessThanEquals(upperBound, upperBoundOfPotentialAllocation), aborter);

			if (check.x) {
				return new Pair<LLVMAssociationIndex, LLVMAbstractState>(pairForLowerBound.x, check.y);
			} else {
				return new Pair<LLVMAssociationIndex, LLVMAbstractState>(null, check.y);
			}
		}

	}

    /**
     * @param term Some simple term (variable or constant) which is a pointer.
     * @param oneMore Is one byte after the allocation ok? If false, the resulting boolean flag must also be false.
     * @return The indices of all allocations to which the specified term may be associated, a flag whether the specified
     *         address is exactly one cell behind the allocation, and the abstract state after this check. The first
     *         component is null if there is no such allocation.
     */
    public Pair<Set<Integer>, LLVMAbstractState> getAssociatedAllocationIndices(
        LLVMTerm term,
        Abortion aborter
    ) {
        final Pair<Set<Integer>, ? extends LLVMIntegerState> res =
            this.getIntegerState().getAssociatedAllocationIndices(
                term,
                aborter
            );
        return new Pair<Set<Integer>, LLVMAbstractState>(res.x, this.setIntegerState(res.y));
    }
    
    
    /**
     * 
     * @param lowerBound
     * @param upperBound
     * @return An allocation [v_1,v_2] which contains [lowerBound,upperBound] or null if no such allocation can be found.
     */
	/* Deleted by Frank, since its a duplicate of getAssociatedAllocationIndex 
	 * public LLVMAssociationIndex getAllocationContaining(LLVMTerm lowerBound, LLVMTerm upperBound, Abortion aborter) {
		LLVMRelationFactory relationFactory = getRelationFactory();
		LLVMTermFactory termFactory = relationFactory.getTermFactory();

		int index = 0;
		for (LLVMAllocation allocation : getAllocations()) {
			if (allocation.x.equals(lowerBound) && allocation.y.equals(upperBound)) {
				return new LLVMAssociationIndex(index, false);
			}
			Pair<Boolean, ? extends LLVMAbstractState> check1 = checkRelation(
					relationFactory.lessThanEquals(allocation.x, lowerBound), aborter);
			if (check1.x) {
				Pair<Boolean, ? extends LLVMAbstractState> check2 = checkRelation(
						relationFactory.lessThanEquals(upperBound, allocation.y), aborter);
				if (check2.x) {
					return new LLVMAssociationIndex(index, false);
				}
			}
			index++;

		}
		return null;

	}*/

    /**
     * @return The call stack.
     */
    public ImmutableDeque<LLVMReturnInformation> getCallStack() {
        return this.callStack;
    }

    /**
     * @return A copy of <code>this</code> where all but the active stack frames have been removed and the allocations of 
     * those lower stack frames are consideres as allocated in the remaining stack frame
     */
    public LLVMAbstractState getCallStackAbstractedState(boolean removeNonLiveVariables, Abortion aborter) {
    	LLVMAbstractState callAbstraction = this.setCallStack(new ArrayDeque<LLVMReturnInformation>(0));
    	callAbstraction = callAbstraction.flagAbstractRecursiveFunctionStart();
    	
    	ImmutableTreeSet<Integer> allStackAllocations = getAllStackAllocatedIndices();
    	
    	LLVMAbstractState resultPriorToPostProcessing = new LLVMAbstractState(
        		callAbstraction.getModule(),
        		callAbstraction.getProgramVariables(),
                allStackAllocations,
                callAbstraction.getProgramPosition(),
                callAbstraction.getCallStack(),
                callAbstraction.isRefined(),
                callAbstraction.getIntegerState(),
                callAbstraction.isAbstractRecursiveFunctionStart(),
                callAbstraction.getAllocatedByMallocIndices(),
                callAbstraction.getTrapValues(),
                callAbstraction.getStrategyParamters(),
                null,
                null //set this manually after call abstracting
            );
    	
    	return resultPriorToPostProcessing.postProcessAfterCallAbstraction(removeNonLiveVariables, aborter).x;
        
        

    }

    /**
     * @return The basic block currently in execution.
     */
    public String getCurrentBlock() {
        return this.getProgramPosition().y;
    }

    /**
     * @return The function currently in execution. (without leading '@')
     */
    public String getCurrentFunction() {
        return this.getProgramPosition().x;
    }

    /**
     * @return The current instruction of this state.
     */
    public LLVMInstruction getCurrentInstruction() {
        return this.getModule().getInstruction(this.getProgramPosition());
    }

    /**
     * @param access The heap range to dereference.
     * @return The invariant for the dereferenced best-fitting heap range in the heap function (null if no fitting
     *         entry is found or the argument was null) and the current state possibly updated during checks.
     */
    public Pair<LLVMSimpleTerm, LLVMAbstractState> getDereferencedAccess(LLVMMemoryRange access, Abortion aborter) {
        if (access == null) {
            return new Pair<LLVMSimpleTerm, LLVMAbstractState>(null, this);
        }
        final Pair<LLVMMemoryRange, ? extends LLVMAbstractState> bestFit = this.findBestContainingHeapRange(access, aborter);
        if (bestFit.x != null) {
            return
                this.getMemory().get(bestFit.x).load(
                    bestFit.y,
                    access.getFromRef(),
                    access.getType(),
                    access.getUnsigned(),
                    aborter
                );
        }
        return new Pair<LLVMSimpleTerm, LLVMAbstractState>(null, bestFit.y);
    }

    /**
     * @param access The heap range to dereference.
     * @return The invariant for the dereferenced heap range in the heap function. Null if there is no entry or the
     *         argument was null.
     */
    public LLVMSimpleTerm getDereferencedAccessSimple(LLVMMemoryRange access, Abortion aborter) {
        if (access == null) {
            return null;
        }
        final ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> theMemory = this.getMemory();
        if (theMemory.containsKey(access)) {
            LLVMMemoryInvariant inv = theMemory.get(access);
            if (inv instanceof LLVMSimpleMemoryInvariant) {
                return ((LLVMSimpleMemoryInvariant)inv).getPointedToValue();
            }
        } else if (access.isPointwise() && this instanceof LLVMHeuristicState) {
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : theMemory.entrySet()) {
                if (entry.getKey() instanceof LLVMMemoryRecursiveRange) {
                    LLVMCombinedMemoryInvariant combInv = (LLVMCombinedMemoryInvariant) entry.getValue();
                    for (LLVMHeuristicRelation rel : ((LLVMHeuristicState)this).getRelations()) {
                        if (rel.getVariables(false).contains(access.getFromRef()) &&
                            rel.getVariables(false).contains(entry.getKey().getFromRef())) {
                            Pair<LLVMHeuristicTerm,Boolean> solve = rel.solveFor((LLVMHeuristicVariable)access.getFromRef());
                            if (solve == null || solve.y != null) {
                                continue;
                            }
                            LLVMHeuristicTerm solvedForAccessRef = solve.x;
                            // search for all fields within this allocation
                            if (solvedForAccessRef.isSumOfVariableAndConstant()) {
                                BigInteger offset = solvedForAccessRef.toLinear().y;
                                return combInv.getValue(offset, access.getType());
                            }
                        }
                    }
                }
            }
            // if access is [ref] with type ty and ref --l-> {0=Inv(ty:v..0;...), ...}, then load v.
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : theMemory.entrySet()) {
                if (entry.getKey() instanceof LLVMMemoryRecursiveRange) {
                    LLVMMemoryRecursiveRange recRange = (LLVMMemoryRecursiveRange) entry.getKey();
                    LLVMCombinedMemoryInvariant combInv = (LLVMCombinedMemoryInvariant) entry.getValue();
                    if (!access.getFromRef().equals(recRange.getFromRef())) {
                        continue;
                    }
                    LLVMSimpleTerm res = combInv.getValue(BigInteger.ZERO, access.getType());
                    if (res != null) {
                        return res;
                    }
                }
            }
        }
        return null;
    }

    /**
     * @param access The simple term to dereference.
     * @param targetType The target type of the dereference.
     * @return The value of the dereferenced term and target type in the heap function. Null if there is no entry or
     *         one of the arguments was null.
     */
    public LLVMSimpleTerm getDereferencedAccessSimple(LLVMSimpleTerm access, LLVMType targetType, boolean unsigned, Abortion aborter) {
        if (access == null || targetType == null) {
            return null;
        }
        return this.getDereferencedAccessSimple(new LLVMMemoryRange(access, access, targetType, unsigned), aborter);
    }


    /**
     * @return The integer state stored in this LLVMAbstractState.
     */
    public LLVMIntegerState getIntegerState() {
        return this.integerState;
    }

    /**
     * @return A set of relations known to hold in a symbolic execution state.
     */
    public Set<LLVMRelation> getInvariants() {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        Set<LLVMRelation> res = new LinkedHashSet<LLVMRelation>();
        for (IntegerRelation rel : this.getIntegerState().toRelationSet()) {
            res.add(relationFactory.createRelation(rel));
        }
        return res;
    }
    
    /**
     * @return The line of the corresponding instruction in the C program. -1 if there is none.
     */
    public int getLineOfCProgram() {
        int line = -1;
        LLVMDebugInformation info = this.getModule().getDebugInformation(this.getCurrentInstruction().getDebugLine());
        if (info != null) {
            line = info.getCLine();
        }
        return line;
    }

    /**
     * @return The live variables.
     */
    public Set<String> getLiveVariables() {
        ImmutableMap<LLVMProgramPosition, ImmutableSet<String>> liveVars = this.getModule().getLiveVariables();
        return liveVars == null ? null : liveVars.get(this.getProgramPosition());
    }

    /**
     * @return The memory function of this state.
     */
    public ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> getMemory() {
        return this.getIntegerState().getMemory();
    }

    /**
     * @return The LLVMModule this state is working on.
     */
    public LLVMModule getModule() {
        return this.module;
    }

    /**
     * @return The number of variables in the variable function of this state.
     */
    public int getNumberOfProgramVariables() {
        return this.getProgramVariables().size();
    }

    /**
     * @return The program counter of this state (within its basic block).
     */
    public int getProgramCounter() {
        return this.getProgramPosition().z;
    }

    /**
     * @return The program position triple containing the name of the function currently in execution, the name of the
     *         basic block currently in execution, and the number of the instruction (program counter, 0 is first
     *         position) within this basic block.
     */
    public LLVMProgramPosition getProgramPosition() {
        return this.programPosition;
    }

    /**
     * @return A map from variable names to references.
     */
    public ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> getProgramVariables() {
        return this.programVariables;
    }

    /**
     * Should only be called for existing variables (will cause NullPointerException otherwise).
     * @param varName The variable's name.
     * @return The variable's type.
     */
    public LLVMType getProgramVariableType(String varName) {
        return this.getProgramVariables().get(varName).y;
    }

    /**
     * @return The relation factory used to build relations for this state.
     */
    public LLVMRelationFactory getRelationFactory() {
        return this.relFact;
    }

    /**
     * Determines the reference for a given literal, if the literal represents a constant or a variable name. This
     * method should only be called for literals whose value is already existing in this state.
     * @param lit The literal to be found.
     * @return The (reference to the) value of the literal.
     */
    public LLVMSimpleTerm getSimpleTermForLiteral(LLVMLiteral lit) {
        // constant
        if (lit instanceof LLVMRegularIntLiteral) {
            return
                this.getRelationFactory().getTermFactory().constant(
                    ((LLVMRegularIntLiteral)lit).getValueAsBigInteger()
                );
        }
        // float constant
        if (lit instanceof LLVMFloatLiteral) {
            return
                this.getRelationFactory().getTermFactory().constant(
                    ((LLVMFloatLiteral)lit).getValue()
                );
        }
        // double constant
        if (lit instanceof LLVMDoubleLiteral) {
            return
                this.getRelationFactory().getTermFactory().constant(
                    ((LLVMDoubleLiteral)lit).getValue()
                );
        }
        // big constant
        // TODO Do we really need both?
        if (lit instanceof LLVMBigIntLiteral) {
            return this.getRelationFactory().getTermFactory().constant(((LLVMBigIntLiteral)lit).getValueAsBigInteger());
        }
        // pointer constant
        if (lit instanceof LLVMNullLiteral) {
            // the null pointer corresponds to a zero integer
            return this.getRelationFactory().getTermFactory().zero();
        }
        // variable
        if (lit instanceof LLVMVariableLiteral) {
            LLVMSymbolicVariable valueRef =
                this.getSymbolicVariableForProgramVariable(((LLVMVariableLiteral)lit).getName());
            if (valueRef == null) {
                // not defined in variable function
                return null;
            } else {
                return valueRef;
            }
        }
        
        if (lit instanceof LLVMGetElementPtrConstExpr) {
        	LLVMGetElementPtrConstExpr gepConst = (LLVMGetElementPtrConstExpr) lit;
            LLVMSymbolicVariable valueRef =
                this.getSymbolicVariableForProgramVariable(gepConst.getPointerLiteral().getName());
            if(gepConst.getIndices().stream().allMatch(l -> (l instanceof LLVMRegularIntLiteral) && ((LLVMRegularIntLiteral) l).getValueAsLong() == 0)
                    || gepConst.getIndices().stream().allMatch(l -> (l instanceof LLVMBigIntLiteral) && ((LLVMBigIntLiteral) l).getValueAsLong() == 0)) {
                return valueRef;
            } else {
            	throw new UnsupportedOperationException("cannot return sum of symbolic var and constant number  here although we would have to!");
            }
        }
        
        
        // should not reach this point,
        // TODO Is this really the reason for not reaching this point (see null return value above)?
        throw new IllegalStateException("Literal value: There should only be a value request if the value exists.");
    }

    /**
     * @return The strategy parameters.
     */
    public LLVMParameters getStrategyParamters() {
        return this.strategyParameters;
    }

    /**
     * @param varName The name of the variable to be found.
     * @return The map entry of the variable in the variable function of this state, else null.
     */
    public LLVMSymbolicVariable getSymbolicVariableForProgramVariable(String varName) {
        ImmutablePair<LLVMSymbolicVariable, LLVMType> entry = this.getProgramVariables().get(varName);
        return entry == null ? null : entry.x;
    }

    /**
     * @return The set of references occurring in this state.
     */
	public Set<LLVMSymbolicVariable> getSymbolicVariables() {
		if (symbolicVariableCache == null) {
			Set<LLVMSymbolicVariable> res = new LinkedHashSet<LLVMSymbolicVariable>();
			for (ImmutablePair<LLVMSymbolicVariable, LLVMType> pair : this.getProgramVariables().values()) {
				res.add(pair.x);
			}
			for (LLVMAllocation allocation : this.getAllocations()) {
				if (allocation.x instanceof LLVMSymbolicVariable) {
					res.add((LLVMSymbolicVariable) allocation.x);
				}
				if (allocation.y instanceof LLVMSymbolicVariable) {
					res.add((LLVMSymbolicVariable) allocation.y);
				}
			}
			for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
				LLVMMemoryRange range = entry.getKey();
				if (range.getFromRef() instanceof LLVMSymbolicVariable) {
					res.add((LLVMSymbolicVariable) range.getFromRef());
				}
				if (range.getToRef() instanceof LLVMSymbolicVariable) {
					res.add((LLVMSymbolicVariable) range.getToRef());
				}
				res.addAll(entry.getValue().getUsedReferences());
			}
			for (LLVMReturnInformation frame : this.getCallStack()) {
				for (ImmutablePair<LLVMSymbolicVariable, LLVMType> pair : frame.getProgramVariables().values()) {
					res.add(pair.x);
				}
			}
			for (IntegerRelation rel : this.getIntegerState().toRelationSet()) {
				Set<? extends IntegerVariable> variablesInRel = rel.getVariables();
				for (IntegerVariable var : variablesInRel) {
					if (var instanceof LLVMSymbolicVariable)
						res.add((LLVMSymbolicVariable) var);
				}

			}
			symbolicVariableCache = ImmutableCreator.create(res);
		}
		return symbolicVariableCache;
	}
	
	
	/**
	 * Returns a set of variables for which we can prove that they are equivalent to the given variable.
	 * The returned set at least includes the given variable
	 * @param variableOfState
	 * @return
	 */
	public ImmutableSet<LLVMSymbolicVariable> getEquivalenceclassOfSymbolicVariable(LLVMSymbolicVariable variableOfState, Abortion aborter) {
		ImmutableSet<LLVMSymbolicVariable> resultFromCache = symbolicVariableEquivalenceClassCache.get(variableOfState);
		
		if(resultFromCache != null) {
			return resultFromCache;
		} else {
			Set<LLVMSymbolicVariable> potentialEquivalenceClass = new LinkedHashSet<>(getSymbolicVariables());
			if(Globals.useAssertions) {
				assert potentialEquivalenceClass.contains(variableOfState);
			}
			Iterator<LLVMSymbolicVariable> variablesOfStateIterator = potentialEquivalenceClass.iterator();
			
			while(variablesOfStateIterator.hasNext()) {
				LLVMSymbolicVariable nextVariable = variablesOfStateIterator.next();
				
				if(nextVariable.equals(variableOfState))
					continue;
				
				if(!checkRelation(relFact.equalTo(variableOfState, nextVariable), aborter).x) {
					variablesOfStateIterator.remove();
				}
			}
			
			ImmutableSet<LLVMSymbolicVariable> immutableResultSet = ImmutableCreator.create(potentialEquivalenceClass);
			
			for(LLVMSymbolicVariable equivalenceClassMember : potentialEquivalenceClass) {
					ImmutableSet<LLVMSymbolicVariable> previousEntry =
							symbolicVariableEquivalenceClassCache.put(equivalenceClassMember, immutableResultSet);
					
					if(Globals.useAssertions) {
						assert previousEntry == null:
							"We should not have seen a member of a class before because it would have been put in this map then";
					}
			}
			return immutableResultSet;
		}
		
	}

    /**
     * @return The possible trap values.
     */
    public ImmutableMap<LLVMSymbolicVariable, LLVMTrapCondition> getTrapValues() {
        return this.possibleTrapValues;
    }

    /**
     * @param var Some symbolic variable.
     * @return A set of all known relations of the form "var type c" or "c type var" where type is any relation type
     *         and c is an integer constant.
     */
    public Set<LLVMRelation> getValueRelations(LLVMSymbolicVariable var) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final Set<LLVMRelation> res = new LinkedHashSet<LLVMRelation>();
        for (IntegerRelation rel : this.getIntegerState().toRelationSet()) {
            if (
                (rel.getLhs().equals(var) && rel.getRhs() instanceof IntegerConstant)
                || (rel.getLhs() instanceof IntegerConstant && rel.getRhs().equals(var))
            ) {
                res.add(relationFactory.createRelation(rel));
            }
        }
        return res;
    }

    /**
     * @return An unrefined AbstractState with a program counter increased by one and everything else as in the current
     *         state.
     */
    public LLVMAbstractState incrementPC() {
        return
            this.setProgramPosition(
                new LLVMProgramPosition(this.getCurrentFunction(), this.getCurrentBlock(), this.getProgramCounter() + 1)
            );
    }

    /**
     * @return This state as initial state.
     */
    public LLVMAbstractState initial(Abortion aborter) {
        final LLVMIntegerState iState = this.getIntegerState();
        if (iState instanceof LLVMDefaultIntegerState) {
            return this.setIntegerState(((LLVMDefaultIntegerState)iState).updateFormula(aborter).x);
        }
        return this;
    }

    /**
     * @return True if this state is the result of a call stack abstraction (omitting all but the topmost stackframe).
     *         False otherwise.
     */
    @Deprecated //do not use any more
    public boolean isAbstractRecursiveFunctionStart() {
        return this.isAbstractRecursiveFunctionStart;
    }

    /**
     * @return True if this is an end state. False otherwise.
     */
    public boolean isEnd() {
        return this.getCurrentInstruction() instanceof LLVMRetInstruction && this.getCallStack().isEmpty();
    }

    /**
     * Is this state an error state?
     * @return True iff this state is an error state.
     */
    public boolean isErrorState() {
        // should be overridden in sub-classes representing error states
        return false;
    }

    /**
     * Is this state an inconsistent state?
     * @return True iff this state is an error state.
     */
    public boolean isInconsistentState() {
        // should be overridden in sub-classes representing error states
        return false;
    }

    /**
     * @param pointerRef The reference to check
     * @return True if pointerRef is the start reference of a struct invariant.
     */
    public boolean isInitialStructPointer(LLVMSymbolicVariable pointerRef) {
        return false;
    }

    /**
     * @param ref Some reference.
     * @return True if the specified reference might be a trap value according to our knowledge. False otherwise.
     */
    public boolean isPossiblyTrapValue(LLVMSimpleTerm ref) {
        return this.possibleTrapValues.containsKey(ref);
    }

    /**
     *
     * @return True iff the current instruction is a call to a function already in the stack
     */
    public boolean isRecursiveCall() {
        if (
            !(this.getCurrentInstruction() instanceof LLVMCallInstruction)
            || this.getCurrentInstruction() instanceof LLVMInvokeInstruction
        ) {
            return false;
        }
        String calledFnName =
            this.getCurrentInstruction() instanceof LLVMCallInstruction ?
                ((LLVMCallInstruction) this.getCurrentInstruction()).getFunctionName().getNameWithoutScope() :
                    ((LLVMInvokeInstruction) this.getCurrentInstruction()).getFunctionName().getNameWithoutScope();
        if (calledFnName.equals(this.getCurrentFunction())) {
            return true;
        }
        for (LLVMReturnInformation retInfo : this.getCallStack()) {
            if (retInfo.getProgPos().x.equals(calledFnName)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Is this state a refinement of another state?
     * @return True iff this state is a refinement.
     */
    public boolean isRefined() {
        return this.refined;
    }
    
    /**
     * Whether or not evaluating the abstract state results in an over-approximated state 
     * 
     * @param aborter The aborter that keeps track if the result is still needed
     * @return <code>false</code> if the evaluation of this state is guaranteed to be no
     * over-approximation
     */
    public boolean isOverapproximation(Abortion aborter) {
        return getCurrentInstruction().isOverapproximation(this, aborter);
    }

    /**
     * @param pointerRef The reference to check
     * @return True if pointerRef is a reference in a struct invariant (e.g., the range reference or the next pointer or the pointer to the next pointer).
     */
    public boolean isStructPointer(LLVMSymbolicVariable pointerRef) {
        return false;
    }

    /**
     * @return A state whose position and variable function are set to the top-most return information in the current
     *         call stack and a call stack like the current one without the top-most element. Moreover, all allocations
     *         known to be within the stack frame are dropped. Everything else is as in the current state.
     */
    public LLVMAbstractState popCallStack(Abortion aborter) {
        // TODO remove heap entries for unallocated memory
        Deque<LLVMReturnInformation> newCallStack = new ArrayDeque<LLVMReturnInformation>(this.getCallStack());
        LLVMReturnInformation inf = newCallStack.pop();
        LLVMAbstractState res =
            this.setProgramVariables(
                inf.getProgramVariables()
            ).setProgramPosition(
                inf.getProgPos()
            ).setCallStack(
                newCallStack
            ).setAllocatedMemoryForAlloca(
                this.getAllocations(),
                inf.getAllocationsInFunction()
            );
        Iterator<Integer> allocIt = this.getAllocatedInCurrentFunctionFrameIndices().descendingIterator();
        while (allocIt.hasNext()) {
            res = res.removeAllocation(allocIt.next(), true, aborter);
        }
        return res;
    }

    /**
     * This method should be called for all states ending up in the symbolic evaluation graph after symbolic execution.
     * @param removeNonLiveVariables Should we remove program variables from the that that are not live (i.e., not read before written?)
     * @return This state after post-processing (e.g., cleaning constraints).
     */
    public LLVMSymbolicEvaluationResult postProcessAfterEvaluation(Set<? extends LLVMRelation> rels, boolean removeNonLiveVariables, Abortion aborter) {
        return this.postProcess(new LLVMSymbolicEvaluationResult(this.setRefined(false), Collections.emptySet()), rels, removeNonLiveVariables, aborter);
    }

    /**
     * This method should be called for all states ending up in the symbolic evaluation graph after generalization.
     * @param removeNonLiveVariables Should we remove program variables from the that that are not live (i.e., not read before written?)
     * @return This state after post-processing (e.g., cleaning constraints).
     */
    public LLVMSymbolicEvaluationResult postProcessAfterGeneralization(boolean removeNonLiveVariables, Abortion aborter) {
    	LLVMSymbolicEvaluationResult postProcessed = this.postProcess(new LLVMSymbolicEvaluationResult(this.setRefined(false), Collections.emptySet()), Collections.emptySet(), removeNonLiveVariables, aborter);
    	if(entryStateVarCorrespondenceMap != null) {
    		LLVMAbstractState readdedEntryStateInfo = LLVMStateBasedSymbolicVariableRenamingRelationEvaluator.generalizationPostProcessing(this, postProcessed.getState());
    		postProcessed = new LLVMSymbolicEvaluationResult(readdedEntryStateInfo, postProcessed.getStateChangeInfo());
    	}
    	return postProcessed;
    }

    /**
     * This method should be called for all states ending up in the symbolic evaluation graph after refinement.
     * @param removeNonLiveVariables Should we remove program variables from the that that are not live (i.e., not read before written?)
     * @return This state after post-processing (e.g., cleaning constraints).
     */
    public LLVMSymbolicEvaluationResult postProcessAfterRefinement(Abortion aborter, boolean removeNonLiveVariables) {
        return this.postProcess(new LLVMSymbolicEvaluationResult(this.setRefined(true), Collections.emptySet()), Collections.emptySet(), removeNonLiveVariables, aborter);
    }
    
    /**
     * This method should be called for all states ending up in the symbolic evaluation graph after state intersection for recursion.
     * @param removeNonLiveVariables Should we remove program variables from the that that are not live (i.e., not read before written?)
     * @return This state after post-processing (e.g., cleaning constraints).
     */
    public LLVMSymbolicEvaluationResult postProcessAfterIntersection(boolean removeNonLiveVariables, Abortion aborter) {
        return this.postProcess(new LLVMSymbolicEvaluationResult(this.setRefined(false), Collections.emptySet()), Collections.emptySet(), removeNonLiveVariables, aborter);    }
    
    /**
     * This method should be called for all states ending up in the symbolic evaluation graph after call abstraction for recursion.
     * @param removeNonLiveVariables Should we remove program variables from the that that are not live (i.e., not read before written?)
     * @return This state after post-processing (e.g., cleaning constraints).
     */
    public LLVMSymbolicEvaluationResult postProcessAfterCallAbstraction(boolean removeNonLiveVariables, Abortion aborter) {
        return this.postProcess(new LLVMSymbolicEvaluationResult(this.setRefined(false), Collections.emptySet()), Collections.emptySet(), removeNonLiveVariables, aborter);    }

    /**
     * @param functionName The name of the called function.
     * @param parameterLiterals The literals passed as parameters of the called function.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return A state with the variable function, position, and last block of the current state pushed as return
     *         information to the call stack, the program position set to the first instruction of the specified
     *         function, and the parameters and heap information initialized according to the current knowledge.
     */
    public LLVMAbstractState pushCallStack(String functionName, List<LLVMLiteral> parameterLiterals, Set<LLVMRelation> newRels, Abortion aborter) {
//        for (ReturnInformation retInfo : this.callStack) {
//            if (retInfo.y.x.equals(functionName)) {
//                throw new UnsupportedOperationException("We cannot handle recursion, yet!");
//            }
//        }
        LLVMFnDeclaration fnDecl = this.getModule().getFunctions().get(functionName);
        if (!(fnDecl instanceof LLVMFnDefinition)) {
            throw new UnsupportedOperationException(
                "We cannot handle calls to only declared functions with parameters!"
            );
        }
        LLVMFnDefinition actFunction = (LLVMFnDefinition)fnDecl;
        // formal function parameters
        List<LLVMFnParameter> parameters = actFunction.getParameters();
        int numOfParams = parameters.size();
        // new variable mapping
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVars =
            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>();
        if (Globals.useAssertions) {
            assert (numOfParams == parameterLiterals.size()) : "Number of parameters does not match!";
        }
        // copy global variables - they are in the scope of the called method
        for (String name: this.getModule().getVariableDefinitions().keySet()) {
            String fullName = "@" + name;
            if (this.getProgramVariables().containsKey(fullName)) {
                newVars.put(fullName, this.getProgramVariables().get(fullName));
            }
        }
        Deque<LLVMReturnInformation> newCallStack = new ArrayDeque<LLVMReturnInformation>(this.getCallStack());
        newCallStack.push(
            new LLVMReturnInformation(
                this.getProgramVariables(),
                this.getProgramPosition(),
                this.getAllocatedInCurrentFunctionFrameIndices()
            )
        );
        LLVMAbstractState res =
            this.setProgramVariables(
                newVars
            ).setAllocatedMemoryForAlloca(
                this.getAllocations(),
                new TreeSet<Integer>()
            ).setProgramPosition(
                new LLVMProgramPosition(functionName, actFunction.getNameOfFirstBlock(), 0)
            ).setCallStack(
                newCallStack
            );
        for (int i = 0; i < numOfParams; i++) {
            LLVMFnParameter param = parameters.get(i);
            LLVMLiteral lit = parameterLiterals.get(i);
            String variableName = "%" + param.getName();
            if (Globals.useAssertions) {
                assert (!newVars.containsKey(variableName)) : "Found two parameters with the same name!";
            }
            res = res.assign(variableName, this.getSimpleTermForLiteral(lit), param.getType(), newRels, aborter);
        }
        return res;
    }

    /**
     * @param trap The reference being a possible trap value.
     * @param condition The condition whose satisfaction would rule out the possibility that <code>trap</code> is a
     *                  trap value.
     * @return The state emerging from this state by adding the specified trap value dependency.
     * @throws UndefinedBehaviorException If the trap value already depends on some condition.
     */
    public LLVMAbstractState putTrapValue(
        LLVMSymbolicVariable trap,
        LLVMTrapCondition condition
    ) throws UndefinedBehaviorException {
        if (this.getTrapValues().containsKey(trap)) {
            throw new UndefinedBehaviorException(
                "We cannot handle this trap value and must assume undefined behavior."
            );
        }
        Map<LLVMSymbolicVariable, LLVMTrapCondition> newTraps =
            new LinkedHashMap<LLVMSymbolicVariable, LLVMTrapCondition>(this.getTrapValues());
        newTraps.put(trap, condition);
        return this.setTrapValues(newTraps);
    }

    /**
     * @param toRemove References and types to be removed from the heap.
     * @return A state where the specified reference/type combinations are removed from the heap, but everything else
     *         is as in the current state.
     */
    public LLVMAbstractState removeHeapAccesses(Collection<LLVMMemoryRange> toRemove) {
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newMemory =
            new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(this.getMemory());
        newMemory.keySet().removeAll(toRemove);
        return this.setMemory(newMemory);
    }

    /**
     * @param keepFunctionParameters TODO
     * @return A state where in the variable function only the live variable entries according to the stored live
     *         variables set are retained and everything else is as in the current state.
     */
    public LLVMAbstractState retainLiveVariables(boolean keepFunctionParameters) {
        return retainLiveVariables(getLiveVariables(), keepFunctionParameters);
    }
    
    /**
     * @param keepFunctionParameters TODO
     * @return A state where in the variable function only the live variable entries according to the stored live
     *         variables set are retained and everything else is as in the current state.
     */
    public LLVMAbstractState retainLiveVariables(Set<String> liveVariables, boolean keepFunctionParameters) {
        if (liveVariables == null) {
            return this;
        }
        Set<String> toKeep = keepFunctionParameters || true ? getModule().getFunctionParameters(getCurrentFunction()) : Collections.emptySet();
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVariableFunction =
            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>();
        boolean allRetained = true;
        for (
            Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> entry :
                this.getProgramVariables().entrySet()
        ) {
            String varName = entry.getKey();
            if (liveVariables.contains(varName) || toKeep.contains(varName)) {
                newVariableFunction.put(varName, entry.getValue());
            } else {
                allRetained = false;
            }
        }
        if (allRetained) {
            return this;
        }
        return this.setProgramVariables(newVariableFunction);
    }
    
    

    /**
     * @return A flag and a state. The flag is true iff this state satisfies the return conditions for its program
     *         position. The state is the current state possibly updated during the checks.
     */
    public Pair<Boolean, ? extends LLVMAbstractState> satisfiesReturnConditions(Abortion aborter) {
        final ImmutableMap<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>> retConds =
            this.getModule().getReturnConditions();
        if (retConds == null) {
            return new Pair<Boolean, LLVMAbstractState>(false, this);
        }
        LLVMAbstractState state = this;
        outer: for (ImmutableSet<IntegerRelation> condition : retConds.get(this.getProgramPosition())) {
            aborter.checkAbortion();
            for (IntegerRelation rel : condition) {
                LLVMRelation replaced = state.replaceSpecialRefs((LLVMRelation)rel);
                Pair<Boolean, ? extends LLVMAbstractState> check = state.checkRelation(replaced, aborter);
                state = check.y;
                if (replaced == null || !check.x) {
                    continue outer;
                }
            }
            return new Pair<Boolean, LLVMAbstractState>(true, state);
        }
        return new Pair<Boolean, LLVMAbstractState>(false, state);
    }

    /**
     * @param from The heap range to map.
     * @param to The invariant to map the heap range to.
     * @return An AbstractState with the new heap mapping put, but everything else as in the current state.
     */
    public LLVMAbstractState setHeapEntry(LLVMMemoryRange from, LLVMMemoryInvariant to) {
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap = new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(this.getMemory());
        newHeap.put(from, to);
        return this.setMemory(newHeap);
    }



    /**
     * @param newProgramPos Some program position.
     * @return A copy of this state where the program position has been replaced by newProgramPos
     */
    public LLVMAbstractState setProgramPosition(LLVMProgramPosition newProgramPos) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                newProgramPos,
                this.getCallStack(),
                this.isRefined(),
                this.getIntegerState(),
                false,
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * @param varName The name of the variable to set.
     * @param ref The variable's reference.
     * @param type The variable's type.
     * @return An AbstractState with the new variable mapping, but everything else as in the current state.
     */
    public LLVMAbstractState setProgramVariable(String varName, LLVMSymbolicVariable ref, LLVMType type) {
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVars =
            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>(this.getProgramVariables());
        ImmutablePair<LLVMSymbolicVariable, LLVMType> previous =
            newVars.put(varName, new ImmutablePair<LLVMSymbolicVariable, LLVMType>(ref, type));
        if (Globals.useAssertions) {
            assert (previous == null || previous.y.equals(type)) : "Tried to change type of a variable!";
        }
        return this.setProgramVariables(newVars);
    }

    /**
     * @param refinedParam The new value of refined.
     * @return An AbstractState with the refined flag set to its parameter and everything else as in the current state.
     */
    public LLVMAbstractState setRefined(boolean refinedParam) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.getCallStack(),
                refinedParam,
                this.getIntegerState(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * @param from The simple term to map.
     * @param targetType The target type for the heap mapping.
     * @param unsigned Is the target type unsigned?
     * @param to The term to map the symbolic variable to.
     * @return An AbstractState with the new heap mapping put, but everything else as in the current state.
     */
    public LLVMAbstractState setSimpleHeapEntry(LLVMSimpleTerm from, LLVMType targetType, boolean unsigned, LLVMTerm to, Abortion aborter) {
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap =
            new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(this.getMemory());
        LLVMSymbolicVariable fresh = this.getRelationFactory().getTermFactory().freshVariable();
        newHeap.put(new LLVMMemoryRange(from, from, targetType, unsigned), new LLVMSimpleMemoryInvariant(fresh));
        return this.setMemory(newHeap).addRelation(this.getRelationFactory().equalTo(fresh, to), aborter);
    }
    
    public CState toCState(int id) {
        int cLine = this.getLineOfCProgram();
        boolean entry = this.getProgramPosition().isFunctionStart(this.getModule());
        String functionName = null;
        if (entry && cLine < 0) {
            LLVMFnDeclaration fnDecl = this.getModule().getFunctions().get(this.getProgramPosition().getFunction());
            LLVMDebugInformation dInfo = this.getModule().getDebugInformation(((LLVMFnDefinition)fnDecl).getDebugLine());
            functionName = dInfo.getFunctionName();
            if (functionName.startsWith("\"")) {
                functionName = functionName.substring(1, 1 + functionName.substring(1).indexOf("\""));
            }
            cLine = dInfo.getCLine();
        }
        entry &= this.getProgramPosition().getFunction().toString().equals("main");
        return new CState(id, cLine, entry, functionName, null);
    }

    @Override
    public String toDOTString() {
        return this.toDOTString(false, -1, null, null, null, null);
    }

    /**
     * @param useHTMLLayout Specifies whether to use the tabular HTML layout or not.
     * @param nodeNumer The number of this node, -1 if no number should be shown.
     * @param functionGraphLabel TODO
     * @param isUnnededNode TODO
     * @param isRecursiveEntryPoint TODO
     * @param predecessor The predecessor/parent node of this state in the graph. Differences between this state and
     *                    the predecessor will be highlighted. May be null if no differences should be highlighted
     *                    (e.g. there are several parents, a generalization was performed, etc.).
     * @return A DOT representation of this state.
     */
    public String toDOTString(
        boolean useHTMLLayout,
        int nodeNumer,
        LLVMAbstractState predecessor,
        String functionGraphLabel,
        Boolean isUnnededNode,
        Boolean isRecursiveEntryPoint
    ) {
        // TODO consider new fields
        if (useHTMLLayout) {
            return
                DOTFormatter.abstractLLVMStateToHTMLDOT(
                    this,
                    predecessor,
                    nodeNumer,
                    functionGraphLabel,
                    isUnnededNode,
                    isRecursiveEntryPoint
                );
        } else {
            /*
             * This is the unchanged previous code for non-html layout. It's still necessary, e.g., for edge labels and
             * backwards compatibility.
             */
            StringBuilder strBuilder = new StringBuilder();
            if (this.isRefined()) {
                strBuilder.append("pos: ");
                strBuilder.append(this.getProgramPosition());
                strBuilder.append(" <refined>\\n");
            } else {
                strBuilder.append("pos: ");
                strBuilder.append(this.getProgramPosition());
                strBuilder.append("\\n");
            }
            strBuilder.append(this.getCurrentInstruction().toDOTString());
            strBuilder.append("\\nvars:\\n");
            final Comparator<Integer> intComp = new Comparator<Integer>(){
                @Override
                public int compare(Integer o1, Integer o2) {
                    return o1 - o2;
                }
            };
            final Comparator<String> nameComp = new LLVMNameComparator();
            strBuilder.append(
                DOTFormatter.toDOT(this.getProgramVariables(), "=", DOTFormatter.BIG_DOT_NL_LIMIT, nameComp)
            );
            strBuilder.append("\\nallocations:\\n");
            strBuilder.append(
                DOTFormatter.toDOT(
                    this.getAllocations(),
                    DOTFormatter.SMALL_DOT_NL_LIMIT,
                    new Comparator<LLVMAllocation>() {

                        @Override
                        public int compare(LLVMAllocation o1, LLVMAllocation o2) {
                            return nameComp.compare(o1.x.getName(), o2.x.getName());
                        }

                    }
                )
            );
            strBuilder.append("\\nheap:\\n");
            strBuilder.append(
                DOTFormatter.toDOT(
                    this.getMemory(),
                    "->",
                    DOTFormatter.BIG_DOT_NL_LIMIT,
                    new Comparator<LLVMMemoryRange>() {

                        @Override
                        public int compare(LLVMMemoryRange o1, LLVMMemoryRange o2) {
                            return nameComp.compare(o1.toString(), o2.toString());
                        }

                    }
                )
            );
            strBuilder.append("\\nknowledge:\\n");
            strBuilder.append(this.getIntegerState().toDOTString());
            strBuilder.append("\\ncall stack:\\n");
            if (this.getCallStack().isEmpty()) {
                strBuilder.append("empty\\n");
            } else {
                for (LLVMReturnInformation retInfo : this.getCallStack()) {
                    strBuilder.append("variables: ");
                    strBuilder.append(
                        DOTFormatter.toDOT(retInfo.getProgramVariables(), "=", DOTFormatter.BIG_DOT_NL_LIMIT, nameComp)
                    );
                    strBuilder.append("\\npos: ");
                    strBuilder.append(retInfo.getProgPos());
                    strBuilder.append("\\nAllocated there: ");
                    strBuilder.append(
                        DOTFormatter.toDOT(retInfo.getAllocationsInFunction(), DOTFormatter.BIG_DOT_NL_LIMIT, intComp)
                    );
                    strBuilder.append("-----\\n");
                }
            }
            return strBuilder.toString();
        }
    }

    /**
     * Encode an abstract state into a function application.
     * @param nodeNumber Used as a label for the outermost function symbol.
     * @param stackRepresentation TODO unused yet
     * @return A term encoding of this state.
     */
    public TRSFunctionApplication toFunctionApplication(
        int nodeNumber,
        TRSTerm stackRepresentation
    ) {
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        // Encode Stack:
//        aprove.verification.dpframework.BasicStructures.Term stack;
//        if (useVarSForStack)
//            stack = aprove.verification.dpframework.BasicStructures.Term.createVariable("s");
//        else
//            stack = aprove.verification.dpframework.BasicStructures.Term.createVariable("s2");
//        if (false) { // was makeRoot
//            aprove.verification.dpframework.BasicStructures.Term eos =
//                aprove.verification.dpframework.BasicStructures.Term.createFunctionApplication(
//                    aprove.verification.dpframework.BasicStructures.FunctionSymbol.create("EOS", 0),
//                    new ArrayList<aprove.verification.dpframework.BasicStructures.Term>(0)
//                );
//            ArrayList<aprove.verification.dpframework.BasicStructures.Term> eosList =
//                new ArrayList<aprove.verification.dpframework.BasicStructures.Term>(1);
//            eosList.add(eos);
//            stack =
//                aprove.verification.dpframework.BasicStructures.Term.createFunctionApplication(
//                    aprove.verification.dpframework.BasicStructures.FunctionSymbol.create(getCurrentFunction(), 1),
//                    eosList
//                );
//        } else {
//            stack = aprove.verification.dpframework.BasicStructures.Term.createVariable("s");
//            if (!variableForStack) {
//                ArrayList<aprove.verification.dpframework.BasicStructures.Term> varStackList =
//                    new ArrayList<aprove.verification.dpframework.BasicStructures.Term>(1);
//                varStackList.add(stack);
//                stack =
//                    aprove.verification.dpframework.BasicStructures.FunctionApplication.createFunctionApplication(
//                        aprove.verification.dpframework.BasicStructures.FunctionSymbol.create(getCurrentFunction(), 1),
//                        varStackList
//                    );
//            }
//        }
        if (stackRepresentation != null) {
            args.add(stackRepresentation);
        }
        for (LLVMSymbolicVariable var : this.getSymbolicVariables()) {
            args.add(var.toTerm());
        }
        return
            TRSTerm.createFunctionApplication(
                FunctionSymbol.create("f_" + nodeNumber, args.size()),
                ImmutableCreator.create(args)
            );
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", "LLVMAbstractState");
        res.put("pos", JSONExportUtil.toJSON(this.getProgramPosition()));
        res.put("curr_instr", JSONExportUtil.toJSON(this.getCurrentInstruction()));
        res.put("variables", JSONExportUtil.toJSON(this.getProgramVariables()));
        res.put("allocs", JSONExportUtil.toJSON(this.getAllocations()));
        res.put("heap", JSONExportUtil.toJSON(this.getMemory()));
        res.put("knowledge", JSONExportUtil.toJSON(this.getIntegerState()));
        res.put("call_stack", JSONExportUtil.toJSON(this.getCallStack()));
        res.put("traps", JSONExportUtil.toJSON(this.getTrapValues()));
        return res;
    }

    @Override
    public String toString() {
        // TODO consider new fields
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("pos: ");
        strBuilder.append(this.getProgramPosition());
        strBuilder.append(" - ");
        strBuilder.append(this.getCurrentInstruction());
        strBuilder.append("\nvariables: ");
        strBuilder.append(this.getProgramVariables());
        strBuilder.append("\nallocated memory areas: ");
        strBuilder.append(this.getAllocations());
        strBuilder.append("\nheap: ");
        strBuilder.append(this.getMemory());
        strBuilder.append("\nknowledge: ");
        strBuilder.append(this.getIntegerState());
        strBuilder.append("\ncall stack:\n");
        if (this.getCallStack().isEmpty()) {
            strBuilder.append("empty\n");
        } else {
            for (LLVMReturnInformation retInfo : this.getCallStack()) {
                strBuilder.append("variables: ");
                strBuilder.append(retInfo.getProgramVariables());
                strBuilder.append("\npos: ");
                strBuilder.append(retInfo.getProgPos());
                strBuilder.append("\nallocated there: ");
                strBuilder.append(retInfo.getAllocationsInFunction());
                strBuilder.append("\n-----\n");
            }
        }
        return strBuilder.toString();
    }
    
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof LLVMAbstractState)) {
            return false;
        }
        LLVMAbstractState other = (LLVMAbstractState)obj;
        if (!this.getProgramPosition().equals(other.getProgramPosition())) {
            return false;
        }
        if (!this.getCurrentInstruction().equals(other.getCurrentInstruction())) {
            return false;
        }
        if (!this.getProgramVariables().equals(other.getProgramVariables())) {
            return false;
        }
        if (!this.getAllocations().equals(other.getAllocations())) {
            return false;
        }
        if (!this.getMemory().equals(other.getMemory())) {
            return false;
        }
        if (!this.getIntegerState().equals(other.getIntegerState())) {
            return false;
        }
        if (this.getCallStack().size() != other.callStack.size()) {
            return false;
        }
        Iterator<LLVMReturnInformation> thisCallStackIt = this.getCallStack().iterator();
        Iterator<LLVMReturnInformation> otherCallStackIt = other.getCallStack().iterator();
        while (thisCallStackIt.hasNext() && otherCallStackIt.hasNext()) {
            if (!thisCallStackIt.next().equals(otherCallStackIt.next())) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return This state where all trap values that could be ruled out are removed.
     */
    public LLVMAbstractState updateTrapValues(Abortion aborter) {
        LLVMAbstractState res = this;
        if (!this.getTrapValues().isEmpty()) {
            boolean changed = false;
            Map<LLVMSymbolicVariable, LLVMTrapCondition> newTraps =
                new LinkedHashMap<LLVMSymbolicVariable, LLVMTrapCondition>(this.getTrapValues());
            for (Map.Entry<LLVMSymbolicVariable, LLVMTrapCondition> trap : this.getTrapValues().entrySet()) {
                final Pair<Boolean, LLVMAbstractState> resolved = trap.getValue().resolved(res, aborter);
                res = resolved.y;
                if (resolved.x) {
                    newTraps.remove(trap.getKey());
                    changed = true;
                }
            }
            if (changed) {
                return res.setTrapValues(newTraps);
            }
        }
        return res;
    }

    /**
     * @param res The evaluation result before post-processing.
     * @param removeNonLiveVariables Should we remove program variables from the that that are not live (i.e., not read before written?)
     * @return The evaluation result after post-processing.
     */
    protected LLVMSymbolicEvaluationResult postProcess(LLVMSymbolicEvaluationResult res, Set<? extends LLVMRelation> rels, boolean removeNonLiveVariables, Abortion aborter) {
        LLVMAbstractState afterPotentiallyRemovingNonLiveVars = removeNonLiveVariables ? res.getState().retainLiveVariables(false) : res.getState();
    	res.setState(afterPotentiallyRemovingNonLiveVars.updateTrapValues(aborter));
        LLVMIntegerState iState = res.getState().getIntegerState();
        if (iState instanceof LLVMDefaultIntegerState) {
            Pair<LLVMDefaultIntegerState, Set<LLVMRelation>> post = ((LLVMDefaultIntegerState)iState).updateFormula(aborter);
            res.setState(res.getState().setIntegerState(post.x));
            if (LLVMDebuggingFlags.ADD_CHANGES_DURING_FORMULA_UPDATE_TO_EDGES) {
                Set<LLVMRelation> stateChangeInfo = new LinkedHashSet<LLVMRelation>(res.getStateChangeInfo());
                stateChangeInfo.addAll(post.y);
                res.setStateChangeInfo(stateChangeInfo);
            }
        }
        return res;
    }

    /**
     * @param index The index of the allocation to be removed.
     * @return This state where the specified allocation has been removed and all allocation indices are updated.
     */
    protected LLVMAbstractState removeAllocation(int index, Abortion aborter) {
        TreeSet<Integer> newAllocatedByMalloc = new TreeSet<Integer>(this.getAllocatedByMallocIndices().headSet(index));
        TreeSet<Integer> newAllocatedInFunction =
            new TreeSet<Integer>(this.getAllocatedInCurrentFunctionFrameIndices().headSet(index));
        List<LLVMAllocation> newAllocations = new ArrayList<LLVMAllocation>(this.getAllocations());
        newAllocations.remove(index);
        for (Integer i : this.getAllocatedByMallocIndices().tailSet(index, false)) {
            newAllocatedByMalloc.add(i - 1);
        }
        for (Integer i : this.getAllocatedInCurrentFunctionFrameIndices().tailSet(index, false)) {
            newAllocatedInFunction.add(i - 1);
        }
        
        ImmutableMap<Integer,Boolean> newAllocationChangedSinceEntryState = null;
        if(allocationChangedSinceEntryState != null) {
        	Map<Integer,Boolean> newMapMutable = new LinkedHashMap<>();
        	for(Map.Entry<Integer, Boolean> e : allocationChangedSinceEntryState.entrySet()) {
        		if(e.getKey() < index) {
        			newMapMutable.put(e.getKey(), e.getValue());
        		} else if(e.getKey() > index) {
        			newMapMutable.put(e.getKey() - 1, e.getValue());
        		}
        	}
        	newAllocationChangedSinceEntryState = ImmutableCreator.create(newMapMutable);
        }
        
        Deque<LLVMReturnInformation> newStack = new ArrayDeque<>();
        for(LLVMReturnInformation stackEntry : callStack) {
        	TreeSet<Integer> newAllocationsOfCurrentStackEntry = new TreeSet<>(stackEntry.getAllocationsInFunction().headSet(index));
        	for (Integer i : stackEntry.getAllocationsInFunction().tailSet(index, false)) {
        		newAllocationsOfCurrentStackEntry.add(i - 1);
            }
        	
        	newStack.add(new LLVMReturnInformation(stackEntry.getProgramVariables(), stackEntry.getProgPos(), ImmutableCreator.create(newAllocationsOfCurrentStackEntry)));
        }
        
        LLVMAbstractState result = this.setAllocatedMemoryForAllocaAndMalloc(newAllocations, newAllocatedInFunction, newAllocatedByMalloc);
        return result.setCallStack(ImmutableCreator.create(newStack)).setAllocationChangedSinceEntryState(newAllocationChangedSinceEntryState);
    }
    
    /**
     * @param index The index of the allocation to be removed.
     * @param removeContainedHeapEntries: If true, we will remove any heap entries within the newly deallocated allocation
     * @return This state where the specified allocation has been removed and all allocation indices are updated.
     */
    protected LLVMAbstractState removeAllocation(int index, boolean removeContainedHeapEntries, Abortion aborter) {
    	LLVMAbstractState removalResult = removeAllocation(index,aborter);
    	return removeContainedHeapEntries ?  removalResult.cleanHeapEntriesWithoutAllocation(aborter): removalResult;
    }

    /**
     * @param newAllocs The allocated areas to set.
     * @param newFrameAllocs The indices of those allocated areas known to be allocated within the current function
     *                       frame.
     * @return A state with the specified allocated areas and everything else as in the current state.
     */
    protected LLVMAbstractState setAllocatedMemoryForAlloca(
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> newFrameAllocs
    ) {
        return this.setAllocatedMemoryForAllocaAndMalloc(newAllocs, newFrameAllocs, this.getAllocatedByMallocIndices());
    }

    /**
     * @param newAllocs The allocated areas to set.
     * @param newFrameAllocs The indices of those allocated areas known to be allocated within the current function
     *                       frame.
     * @param newAllocatedByMalloc The indices of those allocated areas known to be allocated using malloc.
     * @return A state with the specified allocated areas and everything else as in the current state.
     */
    protected LLVMAbstractState setAllocatedMemoryForAllocaAndMalloc(
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> newFrameAllocs,
        TreeSet<Integer> newAllocatedByMalloc
    ) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                ImmutableCreator.create(newFrameAllocs),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                this.getIntegerState().setAllocations(ImmutableCreator.create(newAllocs)),
                this.isAbstractRecursiveFunctionStart(),
                ImmutableCreator.create(newAllocatedByMalloc),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.getAllocationChangedSinceEntryStateMap()
            );
    }

    /**
     * @param newAllocs The allocated areas to set.
     * @param newAllocatedByMalloc The indices of those allocated areas known to be allocated using malloc.
     * @return A state with the specified allocated areas and everything else as in the current state.
     */
    protected LLVMAbstractState setAllocatedMemoryForMalloc(
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> newAllocatedByMalloc
    ) {
        return
            this.setAllocatedMemoryForAllocaAndMalloc(
                newAllocs,
                this.getAllocatedInCurrentFunctionFrameIndices(),
                newAllocatedByMalloc
            );
    }

    /**
     * @param newCallStack The new call stack.
     * @return A state with the specified call stack and everything else as in the current state.
     */
    protected LLVMAbstractState setCallStack(Deque<LLVMReturnInformation> newCallStack) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                ImmutableCreator.create(newCallStack),
                this.isRefined(),
                this.getIntegerState(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * @param iState The new integer state.
     * @return A state where everything is as in the current state except for the integer state. The integer state is
     *         set to the specified integer state.
     */
    protected LLVMAbstractState setIntegerState(LLVMIntegerState iState) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                iState,
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * @param newMemory The memory information to set.
     * @return An AbstractState with the new memory information, but everything else as in the current state.
     */
    protected LLVMAbstractState setMemory(Map<LLVMMemoryRange, LLVMMemoryInvariant> newMemory) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                this.getIntegerState().setMemory(newMemory),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * @param vars The new program variable function.
     * @return This state with the specified program variable function instead of its current one.
     */
    protected LLVMAbstractState setProgramVariables(Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> vars) {
        return
            new LLVMAbstractState(
                this.getModule(),
                ImmutableCreator.create(vars),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                this.getIntegerState(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                this.getTrapValues(),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * @param trapVals The new possible trap values.
     * @return This state where the possible trap values have been set to the specified ones.
     */
    protected LLVMAbstractState setTrapValues(Map<LLVMSymbolicVariable, LLVMTrapCondition> trapVals) {
        return
            new LLVMAbstractState(
                this.getModule(),
                this.getProgramVariables(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.getCallStack(),
                this.isRefined(),
                this.getIntegerState(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                ImmutableCreator.create(trapVals),
                this.getStrategyParamters(),
                null,
                this.allocationChangedSinceEntryState
            );
    }

    /**
     * Tries to find new bigger invariants that became valid due to refinements to refs_that_changes
     * @param refs_that_changed
     * @param params
     * @return
     */
    private LLVMAbstractState findAndJoinFurtherInvariants(Set<LLVMHeuristicVariable> refs_that_changed, Abortion aborter) {
        LLVMAbstractState res = this;
        for (LLVMMemoryRange rng : this.getMemory().keySet()) {
            for (LLVMSymbolicVariable ref_used_by_inf : this.getMemory().get(rng).getUsedReferences()) {
                if (refs_that_changed.contains(ref_used_by_inf)) {
                    res = res.findAndCreateInvariantsForAccess(rng, aborter);
                }
            }
        }
        return res;
    }

    /**
     * Will try to find the best heap range that describes at least the entire range covered by access.
     * It will prefer any heap range with exactly the same bound over all other heap ranges.
     * It will then consider heap ranges where at least one bound is the same.
     * Finally it will look for all heap ranges where access is included.
     * This is done to find the most precise heap range since most ranges will be covered by multiple heap ranges.
     * @param access The heap range to access.
     * @return The best fitting heap range in this.heap that contains access and this state possibly updated during
     *         checks.
     */
    private Pair<LLVMMemoryRange, ? extends LLVMAbstractState> findBestContainingHeapRange(LLVMMemoryRange access, Abortion aborter) {
        final ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> theHeap = this.getMemory();
        for (LLVMMemoryRange other: theHeap.keySet()) {
            if (other.equals(access)) {
                return new Pair<LLVMMemoryRange, LLVMAbstractState>(other, this);
            }
        }
        for (LLVMMemoryRange other : theHeap.keySet()) {
            if (other.getType() == access.getType() && other.getFromRef() == access.getFromRef()) {
                return new Pair<LLVMMemoryRange, LLVMAbstractState>(other, this);
            }
            if (other.getType() == access.getType() && other.getToRef() == access.getToRef()) {
                return new Pair<LLVMMemoryRange, LLVMAbstractState>(other, this);
            }
        }
        LLVMAbstractState state = this;
        for (LLVMMemoryRange other : theHeap.keySet()) {
            if (!other.getType().equals(access.getType())) {
                continue;
            }
            Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(other.getFromRef(), IntegerRelationType.LE, access.getFromRef(), aborter);
            state = check.y;
            if (!check.x) {
                // lower bound does not match
                continue;
            }
            check = state.checkRelation(access.getToRef(), IntegerRelationType.LE, other.getToRef(), aborter);
            state = check.y;
            if (!check.x) {
                // upper bound does not match
                continue;
            }
            return new Pair<LLVMMemoryRange, LLVMAbstractState>(other, state);
        }
        return new Pair<LLVMMemoryRange, LLVMAbstractState>(null, state);
    }

    /**
     * @param rel A pattern relation for a return condition with special refs.
     * @return A relation with the suitable normal references from this state set for the pattern ones. May be null.
     */
    private LLVMRelation replaceSpecialRefs(LLVMRelation rel) {
        Map<LLVMSymbolicVariable, LLVMSimpleTerm> substitution =
            new LinkedHashMap<LLVMSymbolicVariable, LLVMSimpleTerm>();
        for (LLVMSymbolicVariable ref : rel.getVariables()) {
            if (ref instanceof LLVMHeuristicProgVarRef) {
                LLVMSymbolicVariable repRef = this.getSymbolicVariableForProgramVariable(ref.getName());
                if (Globals.useAssertions) {
                    if (substitution.containsKey(ref)) {
                        assert (substitution.get(ref).equals(repRef)) :
                            "Several references for the same variable should be impossible!";
                    }
                }
                if (repRef == null) {
                    return null;
                }
                substitution.put(ref, repRef);
            } else if (ref instanceof LLVMHeapVarRef) {
                ImmutablePair<LLVMSymbolicVariable, LLVMType> var = this.getProgramVariables().get(ref.getName());
                if (var == null) {
                    return null;
                }
                boolean unsigned = false;
                if (this.getStrategyParamters().useBoundedIntegers) {
                    unsigned = this.getModule().getAddressesToUnsignedBitvectorVariables().contains(ref.getName());
                }
                LLVMMemoryInvariant inv =
                    this.getMemory().get(
                        new LLVMMemoryRange(var.x, var.x, ((LLVMPointerType)var.y).getTargetType(), unsigned)
                    );
                if (inv == null || !(inv instanceof LLVMSimpleMemoryInvariant)) {
                    return null;
                }
                LLVMSimpleTerm repRef = ((LLVMSimpleMemoryInvariant)inv).getPointedToValue();
                if (Globals.useAssertions) {
                    if (substitution.containsKey(ref)) {
                        assert (substitution.get(ref).equals(repRef)) :
                            "Several references for the same variable should be impossible!";
                    }
                }
                if (repRef == null) {
                    return null;
                }
                substitution.put(ref, repRef);
            }
        }
        return rel.applySubstitution(substitution);
    }    
    
    
    /**
     * Remove heap entries for which we don't know a allocation containing it.
     */
    public LLVMAbstractState cleanHeapEntriesWithoutAllocation(Abortion aborter) {
    	LLVMAbstractState result = this;
    	
    	for(LLVMMemoryRange heapEntryRange : getIntegerState().getMemory().keySet()) {
    		
    		Pair<LLVMAssociationIndex, LLVMAbstractState> association = result.getAssociatedAllocationIndex(heapEntryRange, aborter);
    		
    		if(association.x == null && !(heapEntryRange instanceof LLVMMemoryRecursiveRange)) {
    			result = result.removeHeapAccesses(Collections.singleton(heapEntryRange));
    		}
    		
    		
    	}
    	
    	return result;
    }
    
    /**
     * Remove interval invariants that are implied by other (larger) interval invariants.
     */
    public LLVMAbstractState cleanHeapInvariants(Abortion aborter) {
        Set<LLVMMemoryRange> toRemove = new LinkedHashSet<LLVMMemoryRange>();
        for (LLVMMemoryRange subset : this.getMemory().keySet()) {
            for (LLVMMemoryRange superset : this.getMemory().keySet()) {
                if (subset.equals(superset)) continue;
                Pair<Boolean, ? extends LLVMAbstractState> startRefCheck =
                    this.checkRelation(subset.getFromRef(), IntegerRelationType.GE, superset.getFromRef(), aborter);
                Pair<Boolean, ? extends LLVMAbstractState> limitRefCheck =
                    this.checkRelation(subset.getToRef(), IntegerRelationType.LE, superset.getToRef(), aborter);
                boolean sameInvariant = this.getMemory().get(subset).equals(this.getMemory().get(superset));
                if (startRefCheck.x && limitRefCheck.x && sameInvariant) {
                    toRemove.add(subset);
                }
            }
        }
        return this.removeHeapAccesses(toRemove);
    }
    
    public String getBottommostFunctionInStack() {
    	String result;
		if(getCallStack().isEmpty()) {
			result = getCurrentFunction();
		} else {
			result = getCallStack().getLast().getProgPos().x;
		}
		
		if(Globals.useAssertions) {
			assert !result.startsWith("@");
		}
		return result;
    }

    
    public ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> getEntryStateVarCorrespondenceMap() {
    	return entryStateVarCorrespondenceMap;
    }
    
    public LLVMAbstractState setVarToEntryStateVarsMap(ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> entryStateVarCorrespondenceMap) {
    	return 
                new LLVMAbstractState(
                        this.getModule(),
                        this.getProgramVariables(),
                        this.getAllocatedInCurrentFunctionFrameIndices(),
                        this.getProgramPosition(),
                        this.getCallStack(),
                        this.isRefined(),
                        this.getIntegerState(),
                        this.isAbstractRecursiveFunctionStart(),
                        this.getAllocatedByMallocIndices(),
                        this.getTrapValues(),
                        this.getStrategyParamters(),
                        entryStateVarCorrespondenceMap,
                        this.allocationChangedSinceEntryState
                    );
    }
    
    public ImmutableMap<Integer,Boolean> getAllocationChangedSinceEntryStateMap() {
    	return allocationChangedSinceEntryState;
    }
    
    public LLVMAbstractState setAllocationChangedSinceEntryState(ImmutableMap<Integer,Boolean> allocationChangedSinceEntryState) {
    	return 
                new LLVMAbstractState(
                        this.getModule(),
                        this.getProgramVariables(),
                        this.getAllocatedInCurrentFunctionFrameIndices(),
                        this.getProgramPosition(),
                        this.getCallStack(),
                        this.isRefined(),
                        this.getIntegerState(),
                        this.isAbstractRecursiveFunctionStart(),
                        this.getAllocatedByMallocIndices(),
                        this.getTrapValues(),
                        this.getStrategyParamters(),
                        this.entryStateVarCorrespondenceMap,
                        allocationChangedSinceEntryState
                    );
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

}


///**
//* TODO do we need extra information?
//* TODO also implement the other way round
//* Creates from this heap an SMT formula with link information. For each variable which is in the heap, a formula
//* is created which describes the pointer connection between the heap variable and the pointer. E.g., if *%x and
//* *%y are in the heap with the same type, then the formula '%x = %y => *%x = *%y' is created.
//* @return An SMT formula with link information.
//*/
//public Formula<SMTLIBTheoryAtom> heapToSMTExtraInformation() {
// Formula<SMTLIBTheoryAtom> formula;
// FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
// List<Formula<SMTLIBTheoryAtom>> smtList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
// Set<HeapRange> remainingHeapKeys = new LinkedHashSet<HeapRange>(this.heap.keySet());
// for (HeapRange heap1 : this.heap.keySet()) {
//     remainingHeapKeys.remove(heap1);
//     for (HeapRange heap2 : remainingHeapKeys) {
//         assert (heap1.getFromRef() == heap1.getToRef());
//         assert (heap2.getFromRef() == heap2.getToRef());
//         if (!heap1.getType().equals(heap2.getType()) || heap1.getFromRef().equals(heap2.getFromRef())) {
//             continue;
//         }
//         SMTLIBIntValue var1Value = heap1.getFromRef().toSMTIntValue();
//         SMTLIBIntValue var2Value = heap2.getFromRef().toSMTIntValue();
//         SMTLIBIntValue var1PointerVal = this.getDereferencedAccessSimple(heap1).toSMTIntValue();
//         SMTLIBIntValue var2PointerVal = this.getDereferencedAccessSimple(heap2).toSMTIntValue();
//         // create formula: %var1 = %var2 => *%var1 = *%var2
//         SMTLIBIntEquals eq1 = SMTLIBIntEquals.create(var1PointerVal, var2PointerVal);
//         SMTLIBIntEquals eq2 = SMTLIBIntEquals.create(var1Value, var2Value);
//         smtList.add(factory.buildImplication(factory.buildTheoryAtom(eq1), factory.buildTheoryAtom(eq2)));
//     }
// }
// formula = factory.buildAnd(smtList);
// return formula;
//}

///**
// * @param access Reference and type to be removed.
// * @return A state emerging from this state by removing the given reference and type entry from the heap.
// * TODO this is buggy - the type of keys does not fit
// */
//public LLVMAbstractState removeHeapAccess(ImmutablePair<LLVMSymbolicVariable, BasicType> access) {
//    Map<HeapRange, Invariant> newHeap = new LinkedHashMap<HeapRange, Invariant>(this.getHeap());
//    newHeap.remove(access);
//    return this.setHeap(newHeap);
//}
