package aprove.input.Programs.llvm.states;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.LLVMMergeResult.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Factory to create heuristic abstract LLVM states that do not emerge from existing states directly.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMHeuristicStateFactory extends LLVMAbstractStateFactory {

    /**
     * The factory to build heuristic LLVM states.
     */
    public static final LLVMHeuristicStateFactory LLVM_HEURISTIC_STATE_FACTORY = new LLVMHeuristicStateFactory();

    
    /**
     * After how many simple merges do we need to introduce smallest/largest value when merging values?
     */
    //This reflects AbstractInt.COUNT_MAX / AbstractBoundedInt.COUNT_MAX
    private static final int MERGE_TO_EXTREME_VALUE_COUNT_THRESHOLD_NORMAL_CONVERGENCE = 2;
    private static final int MERGE_TO_EXTREME_VALUE_COUNT_THRESHOLD_FAST_CONVERGENCE = 1;
    
    
    
    /**
     * @param newResult The generalization result under construction.
     * @param renaming The renaming to convert to a merge substitution.
     * @param instIsNewerState Flag indicating whether instState is the newer state.
     * @return A substitution from ofState references to merged references corresponding to the given renaming.
     */
    private static Map<LLVMHeuristicVariable, LLVMHeuristicVariable> buildMergeSubstitution(
        LLVMMergeResult newResult,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> renaming,
        boolean instIsNewerState
    ) {
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> toResVarMap = new LinkedHashMap<>();
        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> e : renaming.entrySet()) {
            toResVarMap.put(
                e.getKey(),
                (LLVMHeuristicVariable)newResult.getMergedRef(e.getKey(), e.getValue(), !instIsNewerState)
            );
        }
        return toResVarMap;
    }

//    @Override
//    public LLVMHeuristicState createBeginState(
//        LLVMQuery query,
//        LLVMModule module,
//        LLVMParameters params
//    ) {
//        final boolean useBoundedIntegers = params.useBoundedIntegers;
//        final String functionName = query.getFunction();
//        // get function of this instruction
//        FnDeclaration actFuncDecl = module.getFunctions().get(functionName);
//        if (!(actFuncDecl instanceof FnDefinition)) {
//            throw new IllegalArgumentException("Cannot analyze a function without its definition!");
//        }
//        FnDefinition actFunction = (FnDefinition)actFuncDecl;
//        // function parameters
//        List<FnParameter> parameters = actFunction.getParameters();
//        // allocated memory areas
//        List<ImmutablePair<LLVMSymbolicVariable, LLVMSymbolicVariable>> allocMem =
//            new ArrayList<ImmutablePair<LLVMSymbolicVariable, LLVMSymbolicVariable>>();
//        // variable mapping
//        Map<String, ImmutablePair<LLVMSymbolicVariable, BasicType>> newVars =
//            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, BasicType>>();
//        // heap mapping
//        Map<HeapRange, Invariant> newHeap = new LinkedHashMap<HeapRange, Invariant>();
//        // remember named allocated areas - pointers may be associated to the same area
//        Map<String, Integer> namedAreas = new LinkedHashMap<String, Integer>();
//        final int numOfParams = parameters.size();
//        // the reference for the parameter variable
//        LLVMSymbolicVariable[] argumentRefs = new LLVMSymbolicVariable[numOfParams];
//        // marks that the first argument has an allocated area which is at least as big as the second argument (or its
//        // allocated area)
//        Map<Integer, Integer> argumentSizeDependencies = new LinkedHashMap<Integer, Integer>();
//        // associations
//        Map<LLVMHeuristicVariable, Integer> newAssocs = new LinkedHashMap<LLVMHeuristicVariable, Integer>();
//        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets = new LinkedHashMap<LLVMHeuristicVariable, BigInteger>();
//        // value mapping
//        Map<LLVMHeuristicVariable, LLVMValue> newValues = new LinkedHashMap<LLVMHeuristicVariable, LLVMValue>();
//        // relations
//        LLVMHeuristicRelationSet newRels = new LLVMHeuristicRelationSet();
//        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
//        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
//        // TODO Should we choose another representation for global variables?
//        // Note that each global variable points to an allocated area of suitable size.
//        for (Map.Entry<String, GlobalVariable> e : module.getVariableDefinitions().entrySet()) {
//            // Names of global variables start with @.
//            final String name = "@" + e.getKey();
//            GlobalVariable variable = e.getValue();
//            // Create a new pointer that points to the start of some allocated area.
//            BasicType type = variable.getType();
//            // Ensure to set all pointer sizes correctly (should probably be done while parsing).
//            type = type.setSizes(module.getPointerSize());
//            LLVMSymbolicVariable pntr =
//                this.initialKnowledgeForPointer(
//                    name,
//                    new BasicPointerType(type, module.getPointerSize(), null),
//                    newVars,
//                    newValues,
//                    allocMem,
//                    newAssocs,
//                    newAssocOffsets,
//                    true,
//                    useBoundedIntegers,
//                    termFactory
//                );
//            // allocated area contains exactly the global variable
//            newRels.add(
//                relationFactory.equalTo(
//                    termFactory.add(pntr, termFactory.constant(newAssocOffsets.get(pntr))),
//                    allocMem.get(newAssocs.get(pntr)).y
//                )
//            );
//            // set alignment relation, if an alignment is specified
//            if (variable.getAlignment() != null) {
//                int align = variable.getAlignment().toInt();
//                if (align > 1) {
//                    if (Globals.useAssertions) {
//                        // clang requires this; llvm specification seems not to be specific about it.
//                        assert (LLVMIntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
//                    }
//                    newRels.add(
//                        relationFactory.createAlignmentRelation(pntr, termFactory.constant(BigInteger.valueOf(align)))
//                    );
//                }
//            }
//        }
//        // check for all parameters if they are defined and if not, initialize the variables
//        Map<Integer, LLVMHeuristicVariable> initHeapAddrs = new LinkedHashMap<Integer, LLVMHeuristicVariable>();
//        for (int i = 0; i < numOfParams; i++) {
//            // TODO arrays of arrays
//            FnParameter param = parameters.get(i);
//            final String variableName = "%" + param.getName();
//            if (Globals.useAssertions) {
//                assert (!newVars.containsKey(variableName)) : "Found two parameters with the same name!";
//            }
//            BasicType type = param.getType();
//            // if we have a pointer type, the pointer size might not yet be initialized
//            if (type instanceof BasicPointerType) {
//                type =
//                    new BasicPointerType(((BasicPointerType) type).getTargetType(), module.getPointerSize(), null);
//            }
//            QueryInputType queryInputType = query.getType(i);
//            if (queryInputType.isStringType()) {
//                argumentRefs[i] =
//                    this.initialKnowledgeForString(
//                        variableName,
//                        type,
//                        newVars,
//                        newValues,
//                        newHeap,
//                        allocMem,
//                        newAssocs,
//                        newAssocOffsets,
//                        queryInputType.hasMinimalSize(),
//                        initHeapAddrs,
//                        useBoundedIntegers,
//                        termFactory
//                    );
//            } else if (queryInputType.isIntegerType()) {
//                argumentRefs[i] =
//                    this.initialKnowledgeForInteger(
//                        variableName,
//                        type,
//                        newVars,
//                        newValues,
//                        queryInputType.getAnnotation(),
//                        module.getUnsignedVariables(),
//                        useBoundedIntegers,
//                        termFactory
//                    );
//            } else if (queryInputType.isNamedAllocation()) {
//                argumentRefs[i] =
//                    this.initialKnowledgeForNamedArea(
//                        variableName,
//                        type,
//                        newVars,
//                        newValues,
//                        allocMem,
//                        newAssocs,
//                        newAssocOffsets,
//                        queryInputType.getNamedArea(),
//                        namedAreas,
//                        useBoundedIntegers,
//                        termFactory
//                    );
//            } else if (type.isPointerType()) {
//                argumentRefs[i] =
//                    this.initialKnowledgeForPointer(
//                        variableName,
//                        (BasicPointerType)type,
//                        newVars,
//                        newValues,
//                        allocMem,
//                        newAssocs,
//                        newAssocOffsets,
//                        false,
//                        useBoundedIntegers,
//                        termFactory
//                    );
//            } else {
//                argumentRefs[i] =
//                    this.initialKnowledgeForValue(
//                        variableName,
//                        type,
//                        type.getInitializedIntValue(!useBoundedIntegers),
//                        newVars,
//                        newValues,
//                        termFactory
//                    );
//            }
//            if (queryInputType.hasMinimalSize()) {
//                this.addKnowledgeOnAllocatedSize(
//                    queryInputType,
//                    i,
//                    argumentRefs,
//                    allocMem,
//                    newAssocs,
//                    // offsets not relevant here
//                    newRels,
//                    argumentSizeDependencies,
//                    termFactory,
//                    relationFactory
//                );
//            }
//            // create modulo relation for alignment
//            if (type instanceof BasicPointerType) {
//                int align = module.getAbiAlignment(((BasicPointerType)type).getTargetType());
//                if (align > 1) {
//                    if (Globals.useAssertions) {
//                        // clang requires this; llvm specification seems not to be specific about it.
//                        assert (LLVMIntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
//                    }
//                    newRels.add(
//                        relationFactory.createAlignmentRelation(
//                            argumentRefs[i],
//                            termFactory.constant(BigInteger.valueOf(align))
//                        )
//                    );
//                }
//            }
//        }
//        this.handleSizeDependencies(
//            parameters,
//            argumentSizeDependencies,
//            argumentRefs,
//            newRels,
//            allocMem,
//            newAssocs,
//            // offsets not relevant here
//            query,
//            termFactory,
//            relationFactory
//        );
//        // initial states are clean and adjusted by construction
//        return
//            new LLVMHeuristicState(
//                module,
//                ImmutableCreator.create(new TreeSet<Integer>()),
//                new LLVMProgramPosition(functionName, actFunction.getNameOfFirstBlock(), 0),
//                false,
//                new LLVMHeuristicIntegerState(
//                    ImmutableCreator.create(newRels),
//                    ImmutableCreator.create(newValues),
//                    ImmutableCreator.create(Collections.emptySet()),
//                    ImmutableCreator.create(newVars),
//                    ImmutableCreator.create(newHeap),
//                    ImmutableCreator.create(allocMem),
//                    ImmutableCreator.create(newAssocs),
//                    ImmutableCreator.create(newAssocOffsets),
//                    ImmutableCreator.create(new ArrayDeque<ReturnInformation>()),
//                    ImmutableCreator.create(initHeapAddrs),
//                    true,
//                    true
//                ),
//                ImmutableCreator.create(Collections.emptyMap()),
//                false,
//                null, // TODO?
//                ImmutableCreator.create(new TreeSet<Integer>()),
//                params
//            );
//    }

    /**
     * @param newState The newer state.
     * @param oldState The older state.
     * @param newRef The candidate reference in the newer state.
     * @param oldRef The candidate reference in the older state.
     * @param indices The index references in the newer/older state.
     * @param newVal The candidate reference's value in the newer state.
     * @param oldVal The candidate reference's value in the older state.
     * @param mergedRef The merged candidate reference.
     * @param mergedIndex The merged index reference.
     * @return True if it makes sense to look for index relations using the specified candidate references.
     *         False otherwise.
     */
    private static boolean candidateForIndexRelation(
        LLVMHeuristicState newState,
        LLVMHeuristicState oldState,
        LLVMHeuristicVariable newRef,
        LLVMHeuristicVariable oldRef,
        Pair<LLVMSimpleTerm, LLVMSimpleTerm> indices,
        AbstractBoundedInt newVal,
        AbstractBoundedInt oldVal,
        LLVMHeuristicVariable mergedRef,
        LLVMHeuristicVariable mergedIndex,
        Abortion aborter
    ) {
        if (mergedRef == null || mergedRef.equals(mergedIndex)) {
            // this cannot lead to meaningful knowledge
            return false;
        }
        if (!newVal.representsFinitelyManyNumbers() && !oldVal.representsFinitelyManyNumbers()) {
            // otherwise we have a value expansion and should look for index relations
            ImmutableSet<LLVMHeuristicRelation> newRels = newState.getRelations();
            ImmutableSet<LLVMHeuristicRelation> oldRels = oldState.getRelations();
            // still we might have an explicit relation in one state, but not in the other
            boolean newFound = false;
            Boolean newGreater = null;
            Boolean newStrict = null;
            for (LLVMHeuristicRelation rel : newRels) {
                if (!rel.isDirectedInequality() || !rel.isSimple()) {
                    continue;
                }
                LLVMHeuristicVariable left = (LLVMHeuristicVariable)rel.getLhs();
                LLVMHeuristicVariable right = (LLVMHeuristicVariable)rel.getRhs();
                if (left.equals(newRef) && right.equals(indices.x)) {
                    newFound = true;
                    newStrict = rel.isStrictInequality();
                    newGreater = false;
                    break;
                } else if (left.equals(indices.x) && right.equals(newRef)) {
                    newFound = true;
                    newStrict = rel.isStrictInequality();
                    newGreater = true;
                    break;
                }
            }
            boolean oldFound = false;
            Boolean oldGreater = null;
            Boolean oldStrict = null;
            for (LLVMHeuristicRelation rel : oldRels) {
                if (!rel.isDirectedInequality() || !rel.isSimple()) {
                    continue;
                }
                LLVMHeuristicVariable left = (LLVMHeuristicVariable)rel.getLhs();
                LLVMHeuristicVariable right = (LLVMHeuristicVariable)rel.getRhs();
                if (left.equals(oldRef) && right.equals(indices.y)) {
                    oldFound = true;
                    oldStrict = rel.isStrictInequality();
                    oldGreater = false;
                    break;
                } else if (left.equals(indices.y) && right.equals(oldRef)) {
                    oldFound = true;
                    oldStrict = rel.isStrictInequality();
                    oldGreater = true;
                    break;
                }
            }
            if (oldFound || newFound) {
                if (oldFound && newFound) {
                    // only interesting if we do not have the same knowledge, but both relations are in the same
                    // direction
                    if (newGreater == oldGreater && oldStrict != newStrict) {
                        return true;
                    }
                } else {
                    return true;
                }
            }
            // another possibility is that we have a constant offset from the index reference
            for (
                Pair<LLVMHeuristicVariable, BigInteger> pair :
                    LLVMHeuristicStateFactory.computeEqualRefOffsetPairs(newState, newRef, aborter)
            ) {
                if (pair.x.equals(indices.x)) {
                    return true;
                }
            }
            for (
                Pair<LLVMHeuristicVariable, BigInteger> pair :
                    LLVMHeuristicStateFactory.computeEqualRefOffsetPairs(oldState, oldRef, aborter)
            ) {
                if (pair.x.equals(indices.y)) {
                    return true;
                }
            }
            return false;
        }
        return true;
    }

//    /**
//     * @param queryInputType The query type of the i-th parameter.
//     * @param i The index of the parameter.
//     * @param argumentRefs The references for the parameters.
//     * @param allocMem The allocations.
//     * @param newAssocs The associations.
//     * @param newRels The relations.
//     * @param argumentSizeDependencies Marks that the first argument has an allocated area which is at least as big as
//     *                                 the second argument (or its allocated area).
//     * @param termFactory The factory to build terms.
//     * @param relationFactory The factory to build relations.
//     */
//    protected void addKnowledgeOnAllocatedSize(
//        QueryInputType queryInputType,
//        int i,
//        LLVMSymbolicVariable[] argumentRefs,
//        List<ImmutablePair<LLVMSymbolicVariable, LLVMSymbolicVariable>> allocMem,
//        Map<LLVMHeuristicVariable, Integer> newAssocs,
//        LLVMHeuristicRelationSet newRels,
//        Map<Integer, Integer> argumentSizeDependencies,
//        LLVMHeuristicTermFactory termFactory,
//        LLVMHeuristicRelationFactory relationFactory
//    ) {
//        LLVMSymbolicVariable ref = argumentRefs[i];
//        final int allocatedSize = queryInputType.getMinimalSize();
//        if (Globals.useAssertions) {
//            assert (newAssocs.containsKey(ref)) : "Found allocation size for unallocated reference!";
//        }
//        if (queryInputType.isSizeAnArgumentIndex()) {
//            argumentSizeDependencies.put(i, allocatedSize);
//        } else if (allocatedSize > 0) {
//            if (queryInputType.isStringType()) {
//                Integer index = newAssocs.get(ref);
//                ImmutablePair<LLVMSymbolicVariable, LLVMSymbolicVariable> allocation = allocMem.get(index);
//                for (Map.Entry<LLVMHeuristicVariable, Integer> entry : newAssocs.entrySet()) {
//                    LLVMSymbolicVariable key = entry.getKey();
//                    if (entry.getValue().equals(index) && !key.equals(allocation.x) && !key.equals(allocation.y)) {
//                        newRels.add(
//                            relationFactory.lessThanEquals(
//                                termFactory.operation(
//                                    ArithmeticOperationType.ADD,
//                                    key,
//                                    termFactory.constant(BigInteger.valueOf(allocatedSize - 1))
//                                ),
//                                allocation.y
//                            )
//                        );
//                        break;
//                    }
//                }
//            } else {
//                // the i-th parameter is at least alloactedSize bytes away from its upper allocation limit
//                newRels.add(
//                    relationFactory.lessThanEquals(
//                        termFactory.operation(
//                            ArithmeticOperationType.ADD,
//                            ref,
//                            termFactory.constant(BigInteger.valueOf(allocatedSize - 1))
//                        ),
//                        allocMem.get(newAssocs.get(ref)).y
//                    )
//                );
//            }
//        }
//    }

    /**
     * Adds costs for lost heap entries.
     * @param newResult The generalization result currently constructed.
     * @param merged The set of all references in ofState which have been merged at least once.
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @throws TooExpensiveException If this got too expensive...
     */
    private static void checkLossOfHeapInfo(LLVMMergeResult newResult, boolean instIsNewerState, Abortion aborter)
    throws TooExpensiveException {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> mergedHeap = newResult.getGeneralizedState().getMemory();
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> ofHeap = ofState.getMemory();
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> instHeap = instState.getMemory();
        for (LLVMMemoryRange ofRange : ofHeap.keySet()) {
            Set<LLVMSimpleTerm> instLowerPartners = newResult.getRefPartners(ofRange.getFromRef(), instIsNewerState);
            Set<LLVMSimpleTerm> instUpperPartners = newResult.getRefPartners(ofRange.getToRef(), instIsNewerState);
            if (instLowerPartners.isEmpty() || instUpperPartners.isEmpty()) {
                newResult.addCost(LLVMCost.LOST_HEAP_ENTRY, !instIsNewerState);
            } else {
                boolean notFound = true;
                for (LLVMSimpleTerm instLowerRef : instLowerPartners) {
                    for (LLVMSimpleTerm instUpperRef : instUpperPartners) {
                        for (LLVMMemoryRange instRange : instHeap.keySet()) {
                            if (
                                !instRange.getFromRef().equals(instLowerRef)
                                || !instRange.getToRef().equals(instUpperRef)
                                || !ofRange.getType().equals(instRange.getType())
                            ) {
                            continue;
                            }
                            LLVMHeuristicVariable mergedLowerRef =
                                (LLVMHeuristicVariable)
                                    newResult.getMergedRef(instLowerRef, ofRange.getFromRef(), instIsNewerState);
                            LLVMHeuristicVariable mergedUpperRef =
                                (LLVMHeuristicVariable)
                                    newResult.getMergedRef(instUpperRef, ofRange.getToRef(), instIsNewerState);
                            if (mergedLowerRef == null || mergedUpperRef == null) {
                                break;
                            }
                            if (ofRange instanceof LLVMMemoryRecursiveRange) {
                                LLVMHeuristicVariable mergedLength =
                                    (LLVMHeuristicVariable)
                                        newResult.getMergedRef(
                                            ((LLVMMemoryRecursiveRange)instRange).getLength(),
                                            ((LLVMMemoryRecursiveRange)ofRange).getLength(),
                                            instIsNewerState
                                        );
                                if (new LLVMMemoryRecursiveRange(
                                        mergedLowerRef,
                                        mergedUpperRef,
                                        instRange.getType(),
                                        mergedLength
                                    ).isContainedIn(mergedHeap)
                                ) {
                                    notFound = false;
                                }
                            } else {
                                if (mergedHeap.containsKey(
                                        new LLVMMemoryRange(
                                            mergedLowerRef,
                                            mergedUpperRef,
                                            ofRange.getType(),
                                            ofRange.getUnsigned()
                                        )
                                    )
                                ) {
                                    notFound = false;
                                }
                            }
                            break;
                        }
                    }
                }
                if (notFound) {
                    newResult.addCost(LLVMCost.LOST_HEAP_ENTRY, !instIsNewerState);
                }
            }
        }
    }

    /**
     * @param state Some state.
     * @param ref Some reference.
     * @return A TreeSet of pairs of references and constant offsets known to be equal to the specified reference in
     *         the specified state.
     */
    private static TreeSet<Pair<LLVMHeuristicVariable, BigInteger>> computeEqualRefOffsetPairs(
        LLVMHeuristicState state,
        LLVMHeuristicVariable ref,
        Abortion aborter
    ) {
        final LLVMParameters params = state.getStrategyParamters();
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(state.getRelations());
        TreeSet<Pair<LLVMHeuristicVariable,BigInteger>> res =
            new TreeSet<Pair<LLVMHeuristicVariable, BigInteger>>(
                new Comparator<Pair<LLVMHeuristicVariable, BigInteger>>(){

                    @Override
                    public int compare(
                        Pair<LLVMHeuristicVariable, BigInteger> o1,
                        Pair<LLVMHeuristicVariable, BigInteger> o2
                    ) {
                        return o1.y.compareTo(o2.y);
                    }

                }
            );
        Set<Pair<LLVMHeuristicVariable,BigInteger>> next = new LinkedHashSet<Pair<LLVMHeuristicVariable, BigInteger>>();
        next.add(new Pair<LLVMHeuristicVariable, BigInteger>(ref, BigInteger.ZERO));
        LLVMHeuristicRelationSet dumb = new LLVMHeuristicRelationSet();
        while (!next.isEmpty()) {
            res.addAll(next);
            next.clear();
            aborter.checkAbortion();
            for (LLVMHeuristicRelation equation : rels.getEquations()) {
                for (Pair<LLVMHeuristicVariable, BigInteger> pair : res) {
                    Set<LLVMHeuristicTerm> equal =
                        equation.getExpressionsInDirectedInequality(
                            state.getIntegerState(),
                            dumb,
                            pair.x,
                            false,
                            true,
                            params,
                            aborter
                        );
                    equal.retainAll(
                        equation.getExpressionsInDirectedInequality(
                            state.getIntegerState(),
                            dumb,
                            pair.x,
                            false,
                            false,
                            params,
                            aborter
                        )
                    );
                    for (LLVMHeuristicTerm candidate : equal) {
                        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> candidateLinear = candidate.toLinear();
                        if (
                            candidateLinear.x != null
                            && candidateLinear.z.compareTo(BigInteger.ONE) == 0
                            && candidateLinear.x instanceof LLVMHeuristicVariable
                        ) {
                            next.add(
                                new Pair<LLVMHeuristicVariable, BigInteger>(
                                    (LLVMHeuristicVariable)candidateLinear.x,
                                    candidateLinear.y.add(pair.y)
                                )
                            );
                        }
                    }
                }
            }
            next.removeAll(res);
        }
        return res;
    }

    private static void createStructInvariantFromConcrete(
        LLVMMergeResult newResult,
        LLVMSimpleTerm instRef,
        LLVMSimpleTerm ofRef,
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> instStructFields,
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> ofStructFields,
        boolean instIsNewerState,
        boolean aggressive,
        boolean fastConvergence,
        Abortion aborter
    ) throws TooExpensiveException {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        // We are interested in the cases where one of the refs points to (value1, x)
        // and the other points to (value2, someRef), where someRef points to (value3, x).
        // Then, we create an invariant that says that the corresponding ref in the generalized state
        // points (via n pointers) to (value4, x).
        // If value1 = value3, it points (via n pointers) to (value1, x) and we try to create
        // an additional invariant for the values in between.
        LLVMSimpleTerm genRef = newResult.getMergedRef(instRef, ofRef, instIsNewerState);
        if (!aggressive && newResult.getGeneralizedState().getAssociatedAllocationIndices(genRef, aborter).x.isEmpty()) {
            return;
        }
        LLVMHeuristicVariable ofLastPtr = ofState.getStructLastPtr(ofStructFields);
        BigInteger ofLength = ofState.getStructLength(ofStructFields, ofLastPtr);
        AbstractInt ofLengthLit;
        if (ofLength == null) {
            return;
        } else {
            ofLengthLit = LiteralInt.create(ofLength);
        }
        LLVMHeuristicVariable instLastPtr = instState.getStructLastPtr(instStructFields);
        BigInteger instLength = instState.getStructLength(instStructFields, instLastPtr);
        AbstractInt instLengthLit;
        if (instLength == null) {
            return;
        } else {
            instLengthLit = LiteralInt.create(instLength);
        }
        if (instLength.equals(ofLength)) return;
        LLVMTermFactory termFactory = newResult.getGeneralizedState().getRelationFactory().getTermFactory();
        LLVMHeuristicVariable mergedLengthRef;
        LLVMSimpleTerm existingVar = null;
        if (instLength != null && ofLength != null) {
            existingVar = newResult.getMergedRef(termFactory.constant(instLength), termFactory.constant(ofLength), instIsNewerState);
        }
        if (existingVar != null && existingVar instanceof LLVMHeuristicVariable) {
            mergedLengthRef = (LLVMHeuristicVariable) existingVar;
        } else {
            LLVMValue mergedLength =
                mergeValues(
                    newResult,
                    instLengthLit,
                    ofLengthLit,
                    IntegerType.UI32,
                    instIsNewerState,
                    fastConvergence
                );
            mergedLengthRef = (LLVMHeuristicVariable) termFactory.freshVariable();
            newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue(mergedLengthRef, mergedLength));
        }
        // structfields: find allocIndices of all ptr-refs
        LLVMSimpleTerm next =
            newResult.getMergedRef(
                instState.getStructNext(instStructFields),
                ofState.getStructNext(ofStructFields),
                instIsNewerState
            );
        LLVMSimpleTerm last =
            newResult.getMergedRef(
                instState.getStructLastPtr(instStructFields),
                ofState.getStructLastPtr(ofStructFields),
                instIsNewerState
            );
        LLVMMemoryRange mergedRange = new LLVMMemoryRecursiveRange(genRef, genRef, getStructTypes(instStructFields), mergedLengthRef);
        Map<BigInteger,LLVMMemoryInvariant> offsetToInv = new LinkedHashMap<BigInteger,LLVMMemoryInvariant>();
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : ofStructFields) {
            BigInteger offset = triple.x;
            LLVMType type = triple.y;
            LLVMMemoryInvariant inv = null;
            if (triple.y.isPointerType() &&
                    (((LLVMPointerType)triple.y).getTargetType().isStructureType() || (((LLVMPointerType)triple.y).getTargetType() instanceof LLVMNamedType))) {
                inv = new LLVMComplexMemoryInvariant(next, last, new LLVMAdditiveChange(null), type);
            } else {
                List<LLVMSymbolicVariable> ofValues = ofState.getStructValues(ofStructFields, offset, ofLastPtr);
                List<LLVMSymbolicVariable> instValues = instState.getStructValues(instStructFields, offset, instLastPtr);
                // search for variables with exactly the first or the last values to infer invariant
                // -> collect all concrete references that match the value type
                Map<LLVMHeuristicVariable,Pair<BigInteger,BigInteger>> varOfInst = new LinkedHashMap<LLVMHeuristicVariable,Pair<BigInteger,BigInteger>>();
                for (Map.Entry<String,ImmutablePair<LLVMSymbolicVariable,LLVMType>> ofVar : ofState.getProgramVariables().entrySet()) {
                    if (ofVar.getValue().y.equals(type) && ((LLVMHeuristicVariable)ofVar.getValue().x).isConcrete()) {
                        LLVMHeuristicVariable instVar = instState.getSymbolicVariableForProgramVariable(ofVar.getKey());
                        if (instVar.isConcrete()) {
                            varOfInst.put(
                                ((LLVMHeuristicState)newResult.getGeneralizedState()).getSymbolicVariableForProgramVariable(ofVar.getKey()),
                                new Pair<BigInteger,BigInteger>(
                                    ((LLVMConstant)ofVar.getValue().x).getIntegerValue(),
                                    ((LLVMConstant)instVar).getIntegerValue()
                                )
                            );
                        }
                    }
                }
                inv =
                    LLVMComplexMemoryInvariant.deduce(
                        ofState.getRelations(),
                        instState.getRelations(),
                        ofValues,
                        instValues,
                        type,
                        varOfInst,
                        newResult,
                        instIsNewerState
                    );
                if (inv == null) assert false;
            }
            offsetToInv.put(offset,inv);
        }
        LLVMMemoryInvariant mergedInvariant = new LLVMCombinedMemoryInvariant(offsetToInv);
        newResult.setGeneralizedState(
                newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
        );
        // remove list allocations and associations from generalized state
        Set<Integer> sharedAllocs = new HashSet<>();
        sharedAllocs.addAll(newResult.getGeneralizedState().getAssociatedAllocationIndices(next, aborter).x);
        sharedAllocs.addAll(newResult.getGeneralizedState().getAssociatedAllocationIndices(genRef, aborter).x);
        while (sharedAllocs != null && !sharedAllocs.isEmpty()) {
            int i = sharedAllocs.iterator().next();
            newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).removeAllocation(i, aborter));
            newResult.removeMergeAreaEntry(i);
            sharedAllocs = new HashSet<>();
            sharedAllocs.addAll(newResult.getGeneralizedState().getAssociatedAllocationIndices(next, aborter).x);
            sharedAllocs.addAll(newResult.getGeneralizedState().getAssociatedAllocationIndices(genRef, aborter).x);
        }
    }

    private static void createStructInvariantFromConcreteAndInvariant(
        LLVMMergeResult newResult,
        LLVMSimpleTerm instRef,
        LLVMSimpleTerm ofRef,
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> instStructFields,
        LLVMMemoryRecursiveRange ofRange,
        LLVMCombinedMemoryInvariant ofInv,
        boolean instIsNewerState,
        boolean fastConvergence,
        Abortion aborter
    ) throws TooExpensiveException {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMSimpleTerm genRef = newResult.getMergedRef(instRef, ofRef, instIsNewerState);
        LLVMHeuristicVariable ofLength = (LLVMHeuristicVariable) ofRange.getLength();
        LLVMHeuristicVariable instLastPtr = instState.getStructLastPtr(instStructFields);
        BigInteger instLength = instState.getStructLength(instStructFields, instLastPtr);
        if (instRef.equals(instState.getStructNext(instStructFields))) {
            instLength = BigInteger.ONE;
        }
        AbstractInt instLengthLit;
        if (instLength == null) {
            return;
        } else {
            instLengthLit = LiteralInt.create(instLength);
        }
        LLVMTermFactory termFactory = newResult.getGeneralizedState().getRelationFactory().getTermFactory();
        LLVMHeuristicVariable mergedLengthRef;
        LLVMSimpleTerm existingVar = null;
        if (instLength != null && ofLength != null) {
            existingVar = newResult.getMergedRef(termFactory.constant(instLength), ofLength, instIsNewerState);
        }
        if (existingVar != null && existingVar instanceof LLVMHeuristicVariable) {
            mergedLengthRef = (LLVMHeuristicVariable) existingVar;
        } else {
            LLVMValue mergedLength =
                mergeValues(
                    newResult,
                    instLengthLit,
                    ofState.getValue(ofLength),
                    IntegerType.UI32,
                    instIsNewerState,
                    fastConvergence
                );
            mergedLengthRef = (LLVMHeuristicVariable) termFactory.freshVariable();
            newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue(mergedLengthRef, mergedLength));
        }
        LLVMMemoryRange mergedRange = new LLVMMemoryRecursiveRange(genRef, genRef, getStructTypes(instStructFields), mergedLengthRef);
        Map<BigInteger,LLVMMemoryInvariant> offsetToInv = new LinkedHashMap<BigInteger,LLVMMemoryInvariant>();
        
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : instStructFields) {
            BigInteger offset = triple.x;
            LLVMType type = triple.y;
            LLVMComplexMemoryInvariant ofInvWithOffset = (LLVMComplexMemoryInvariant) ofInv.getInvariantWithOffset(offset);
            List<LLVMSymbolicVariable> instValues = instState.getStructValues(instStructFields, offset, instLastPtr);
            LLVMSimpleTerm first =
                newResult.getMergedRef(
                    instValues.get(0),
                    ofInvWithOffset.getFirstValue(),
                    instIsNewerState
                );
            if (first == null) {
                LLVMValue mergedFirst =
                    mergeValues(
                        newResult,
                        instState.getValue((LLVMHeuristicVariable)instValues.get(0)),
                        ofState.getValue((LLVMHeuristicVariable)ofInvWithOffset.getFirstValue()),
                        ofInvWithOffset.getType().getIntegerType(instIsNewerState, fastConvergence),
                        instIsNewerState,
                        fastConvergence
                    );
                first = (LLVMHeuristicVariable) termFactory.freshVariable();
                newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue((LLVMHeuristicVariable)first, mergedFirst));
            }
            LLVMSimpleTerm last =
                newResult.getMergedRef(
                    instValues.get(instValues.size()-1),
                    ofInvWithOffset.getLastValue(),
                    instIsNewerState
                );
            if (last == null) {
                LLVMValue mergedLast =
                    mergeValues(
                        newResult,
                        instState.getValue((LLVMHeuristicVariable)instValues.get(instValues.size()-1)),
                        ofState.getValue((LLVMHeuristicVariable)ofInvWithOffset.getLastValue()),
                        ofInvWithOffset.getType().getIntegerType(instIsNewerState, fastConvergence),
                        instIsNewerState,
                        fastConvergence
                    );
                last = (LLVMHeuristicVariable) termFactory.freshVariable();
                newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue((LLVMHeuristicVariable)last, mergedLast));
            }
            LLVMAdditiveChange change = ofInvWithOffset.getChange();
            if (change.getLinearRate() != null) {
                LLVMSimpleTerm ofChange = termFactory.constant(change.getLinearRate());
                for (int i = 0; i < instValues.size()-1; i++) {
                    LLVMTerm instChange = termFactory.sub(instValues.get(i+1), instValues.get(i));
                    if (!instState.checkRelation(instChange, IntegerRelationType.EQ, ofChange, aborter).x) {
                        change = new LLVMAdditiveChange(null);
                        break;
                    }
                }
            }
            if (change.getLinearRate() == null) {
                LLVMSortedType instSortedType = ofInvWithOffset.getChange().getSortedType();
                for (int i = 0; i < instValues.size()-1; i++) {
                    if (instSortedType == LLVMSortedType.ASCENDING) {
                        if (!instState.checkRelation(instValues.get(i), IntegerRelationType.LT, instValues.get(i+1), aborter).x) {
                            if (instState.checkRelation(instValues.get(i), IntegerRelationType.LE, instValues.get(i+1), aborter).x) {
                                instSortedType = LLVMSortedType.NONDESCENDING;
                            } else {
                                instSortedType = LLVMSortedType.UNSORTED;
                                break;
                            }
                        }
                    } else if (instSortedType == LLVMSortedType.DESCENDING) {
                        if (!instState.checkRelation(instValues.get(i+1), IntegerRelationType.LT, instValues.get(i), aborter).x) {
                            if (instState.checkRelation(instValues.get(i+1), IntegerRelationType.LE, instValues.get(i), aborter).x) {
                                instSortedType = LLVMSortedType.NONASCENDING;
                            } else {
                                instSortedType = LLVMSortedType.UNSORTED;
                                break;
                            }
                        }
                    } else if (instSortedType == LLVMSortedType.NONASCENDING) {
                        if (!instState.checkRelation(instValues.get(i+1), IntegerRelationType.LE, instValues.get(i), aborter).x) {
                            instSortedType = LLVMSortedType.UNSORTED;
                            break;
                        }
                    } else if (instSortedType == LLVMSortedType.NONDESCENDING) {
                        if (!instState.checkRelation(instValues.get(i), IntegerRelationType.LE, instValues.get(i+1), aborter).x) {
                            instSortedType = LLVMSortedType.UNSORTED;
                            break;
                        }
                    }
                }
                change = new LLVMAdditiveChange(null, instSortedType);
            }
            LLVMMemoryInvariant inv = new LLVMComplexMemoryInvariant(first, last, change, type);
            offsetToInv.put(offset,inv);
        }
        
        LLVMMemoryInvariant mergedInvariant = new LLVMCombinedMemoryInvariant(offsetToInv);
        newResult.setGeneralizedState(
                newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
        );
        // removal of list allocations and associations from generalized state should not be necessary
    }

    /**
     * Tries to find corresponding heap entries pointing to structs and merges the respective references such that they point to a struct of variable length.
     * @param newResult The generalization result currently constructed.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @throws TooExpensiveException If this got too expensive.
     */
    private static void deduceStructHeapInvariants(
        LLVMMergeResult newResult,
        boolean instIsNewerState,
        boolean aggressive,
        boolean fastConvergence,
        Abortion aborter
    ) throws TooExpensiveException {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        // added contains all references which have already been merged (at least once)
        Set<LLVMSimpleTerm> added = new LinkedHashSet<LLVMSimpleTerm>(newResult.getMergedOfRefs(instIsNewerState));
        Queue<LLVMSimpleTerm> todo = new ArrayDeque<LLVMSimpleTerm>(added);
        while (!todo.isEmpty()) {
            LLVMSimpleTerm ofRef = todo.poll();
            if (!(ofRef instanceof LLVMHeuristicVarRef)) {
                continue;
            }
            Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> ofStructFields =
                    ofState.getStructFields((LLVMHeuristicVarRef)ofRef);
            Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> instStructFields = null;
            LLVMSimpleTerm instRef = null;
            for (LLVMSimpleTerm ref : newResult.getRefPartners(ofRef, instIsNewerState)) {
                if (!(ref instanceof LLVMHeuristicVarRef)) {
                    continue;
                }
                instStructFields = instState.getStructFields((LLVMHeuristicVarRef)ref);
                instRef = ref;
            }
            if (ofRef != null && ofRef.equals(ofState.getStructNext(ofStructFields)) && instStructFields != null && instState.getStructLastPtr(instStructFields) != null) {
                throw new TooExpensiveException("Trying to merge cyclic list of length 1 with noncyclic list!");
            }
            if (instRef != null && instRef.equals(instState.getStructNext(instStructFields)) && ofStructFields != null && ofState.getStructLastPtr(ofStructFields) != null) {
                throw new TooExpensiveException("Trying to merge cyclic list of length 1 with noncyclic list!");
            }
            if (ofStructFields == null && instStructFields != null) {
                for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> ofEntry : ofState.getMemory().entrySet()) {
                    if (!(ofEntry.getKey() instanceof LLVMMemoryRecursiveRange) || !(ofEntry.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                        continue;
                    }
                    LLVMMemoryRecursiveRange ofRange = (LLVMMemoryRecursiveRange) ofEntry.getKey();
                    if (!ofRange.getFromRef().equals(ofRef)) {
                        continue;
                    }
                    if (ofState.checkRelation(ofRange.getLength(), IntegerRelationType.GT, ofState.getRelationFactory().getTermFactory().one(), aborter).x) {
                        // list in ofState has length > 2
                        if (instRef.equals(instState.getStructNext(instStructFields))) {
                            // list in instState is cyclic with only one element
                            throw new TooExpensiveException("Trying to merge cyclic list of length 1 with cyclic list of length > 1!");
                        }
                    }
                }
            }
            if (ofRef.equals(ofState.getStructNext(ofStructFields))) {
                // list in ofState is cyclic and has length 1
                for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> instEntry : instState.getMemory().entrySet()) {
                    if (!(instEntry.getKey() instanceof LLVMMemoryRecursiveRange) || !(instEntry.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                        continue;
                    }
                    LLVMCombinedMemoryInvariant instInv = (LLVMCombinedMemoryInvariant) instEntry.getValue();
                    if (instEntry.getKey().getFromRef().equals(instRef) && !instRef.equals(instInv.getLastRecursivePointer())) {
                        // there already exists a list invariant in instState which is non-cyclic
                        throw new TooExpensiveException("Trying to merge cyclic list of length 1 with non-cyclic list!");
                    }
                }
            }
            if (ofStructFields != null) {
                for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> ofEntry : ofState.getMemory().entrySet()) {
                    if (!(ofEntry.getKey() instanceof LLVMMemoryRecursiveRange) || !(ofEntry.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                        continue;
                    }
                    LLVMCombinedMemoryInvariant ofInv = (LLVMCombinedMemoryInvariant) ofEntry.getValue();
                    for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> instEntry : instState.getMemory().entrySet()) {
                        if (!(instEntry.getKey() instanceof LLVMMemoryRecursiveRange)) {
                            continue;
                        }
                        LLVMCombinedMemoryInvariant instInv = (LLVMCombinedMemoryInvariant) instEntry.getValue();
                        if (ofEntry.getKey().getFromRef().equals(ofInv.getLastRecursivePointer())
                                && !instEntry.getKey().getFromRef().equals(instInv.getLastRecursivePointer())
                                || (!ofEntry.getKey().getFromRef().equals(ofInv.getLastRecursivePointer())
                                        && instEntry.getKey().getFromRef().equals(instInv.getLastRecursivePointer()))) {
                            throw new TooExpensiveException("Trying to merge cyclic list invariant with non-cyclic list invariant!");
                        }
                        if (instEntry.getKey().getFromRef().equals(instRef)) {
                            if (instState.containsStructElementPointingTo(instRef, ofInv.getOffsetOfRecPointer(), aborter)) {
                                continue;
                            }
                            if (ofEntry.getKey().getFromRef().equals(ofState.getStructNext(ofStructFields))) {
                                if (!aggressive) {
                                    throw new TooExpensiveException("Merging will lose first part of traversed list!");
                                }
                            }
                            if (ofState.getStructNext(ofStructFields) != null && ofState.getStructNext(ofStructFields) instanceof LLVMHeuristicVarRef) {
                                LLVMHeuristicVarRef next = (LLVMHeuristicVarRef) ofState.getStructNext(ofStructFields);
                                if (ofEntry.getKey().getFromRef().equals(ofState.getStructNext(next))) {
                                    if (!aggressive) {
                                        throw new TooExpensiveException("Merging will lose first part of traversed list!");
                                    }
                                }
                                if (ofState.getStructNext(next) != null && ofState.getStructNext(next) instanceof LLVMHeuristicVarRef) {
                                    LLVMHeuristicVarRef nextnext = (LLVMHeuristicVarRef) ofState.getStructNext(next);
                                    if (ofEntry.getKey().getFromRef().equals(ofState.getStructNext(nextnext))) {
                                        if (!aggressive) {
                                            throw new TooExpensiveException("Merging will lose first part of traversed list!");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            // When merging aggressively, also merge list invariants with concrete lists.
            if (aggressive && instStructFields != null && !instState.containsStructWithStartPointer(instRef, aborter) && ofStructFields == null) {
                outer: for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> ofEntry : ofState.getMemory().entrySet()) {
                    if (!(ofEntry.getKey() instanceof LLVMMemoryRecursiveRange) || !(ofEntry.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                        continue;
                    }
                    LLVMMemoryRecursiveRange ofRange = (LLVMMemoryRecursiveRange) ofEntry.getKey();
                    if (!ofRange.getFromRef().equals(ofRef)) {
                        continue;
                    }
                    LLVMCombinedMemoryInvariant ofInv = (LLVMCombinedMemoryInvariant) ofEntry.getValue();
                    for (LLVMSimpleTerm instPartner : newResult.getRefPartners(instRef, !instIsNewerState)) {
                        LLVMSimpleTerm mergedRef = newResult.getMergedRef(instRef, instPartner, instIsNewerState);
                        if (newResult.getGeneralizedState().isStructPointer((LLVMSymbolicVariable)mergedRef)) {
                            // instRef has already been used for a reference in a merged struct invariant!
                            // we may only use instRef as a list of size 0
                            continue outer;
                        }
                    }
                    for (LLVMSimpleTerm ofPartner : newResult.getRefPartners(ofRef, instIsNewerState)) {
                        LLVMSimpleTerm mergedRef = newResult.getMergedRef(ofPartner, ofRef, instIsNewerState);
                        if (newResult.getGeneralizedState().isStructPointer((LLVMSymbolicVariable)mergedRef)) {
                            // ofRef has already been used for a reference in a merged struct invariant!
                            // we may only use ofRef as a list of size 0
                            continue outer;
                        }
                    }
                    createStructInvariantFromConcreteAndInvariant(
                        newResult,
                        instRef,
                        ofRef,
                        instStructFields,
                        ofRange,
                        ofInv,
                        instIsNewerState,
                        fastConvergence,
                        aborter
                    );
                }
            }
            if (ofStructFields == null || instStructFields ==  null) {
                continue;
            }
            if (!isCompatibleStruct(instStructFields, ofStructFields)) {
                continue;
            }
            createStructInvariantFromConcrete(
                newResult,
                instRef,
                ofRef,
                instStructFields,
                ofStructFields,
                instIsNewerState,
                aggressive,
                fastConvergence,
                aborter
            );
        }
    }

    /**
     * If a relation also holds for a smaller offset, we either already have the information or we need to generalize
     * here. In any case we must then throw away the relation.
     * @param state An abstract state.
     * @param rel A relation.
     * @return True if the given relation is a directed inequality with some constant offset greater than 0 which holds
     *         in the specified state with a smaller offset. False otherwise.
     */
    private static boolean directedInequalityHoldsForSmallerOffset(
        LLVMHeuristicState state,
        LLVMHeuristicRelation rel,
        Abortion aborter
    ) {
        if (!rel.isDirectedInequality()) {
            return false;
        }
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
        if (lhsLinear.y.compareTo(BigInteger.ZERO) == 0) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
            if (rhsLinear.y.compareTo(BigInteger.ZERO) == 0) {
                // offset is zero
                return false;
            }
        }
        final LLVMHeuristicTermFactory termFactory = state.getRelationFactory().getTermFactory();
        return
            state.getIntegerState().truthValueOfRelation(
                termFactory.add(termFactory.one(), rel.getLhs()),
                rel.getHeuristicRelationType(),
                rel.getRhs(),
                true,
                aborter
            ) == YNM.YES;
    }

    /**
     * @param rels The relations.
     * @param allocations The allocations.
     * @param ref The reference.
     * @return A set of allocations (a,b), references x, and offsets c where the relations contain a relation ref < b
     *         and imply ref + 1 = a + c = x <= b.
     */
    private static Set<AllocationLimitOffset> findAllocsWithGreaterUpperAndOffset(
        LLVMHeuristicRelationSet rels,
        ImmutableList<LLVMAllocation> allocations,
        LLVMHeuristicVarRef ref
    ) {
        Set<AllocationLimitOffset> res = new LinkedHashSet<AllocationLimitOffset>();
        LLVMHeuristicVariable x = null;
        for (LLVMHeuristicRelation equation : rels.getEquations()) {
            Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> pattern =
                equation.toOffByConstantPattern();
            if (pattern == null) {
                continue;
            }
            if (pattern.x.equals(ref) && pattern.z.compareTo(BigInteger.ONE) == 0) {
                x = pattern.y;
                break;
            } else if (pattern.y.equals(ref) && pattern.z.compareTo(IntegerUtils.NEGONE) == 0) {
                x = pattern.x;
                break;
            }
        }
        if (x == null) {
            return Collections.<AllocationLimitOffset>emptySet();
        }
        for (LLVMHeuristicRelation rel : rels.getStrictDirectedInequalities()) {
            if (!rel.isSimple() || !ref.equals(rel.getLhs())) {
                continue;
            }
            LLVMHeuristicTerm rhs = rel.getRhs();
            for (LLVMAllocation allocation : allocations) {
                if (rhs.equals(allocation.y)) {
                    BigInteger offset =
                        LLVMHeuristicStateFactory.hasKnownOffset(
                            rels,
                            (LLVMHeuristicVariable)allocation.x,
                            ref,
                            BigInteger.ZERO,
                            true
                        );
                    if (offset != null) {
                        res.add(new AllocationLimitOffset(allocation, x, offset.add(BigInteger.ONE)));
                    }
                    break;
                }
            }
        }
        return res;
    }

    /**
     * @param newResult The generalization result under construction.
     * @param ofRefs Set of references to find renamings for (from the ofState).
     * @param instIsNewerState Flag indicating whether the instState is the newer state.
     * @param tolerateRefsWithoutPartner Flag indicating whether no renaming should be returned if there is some
     *                                   reference without a partner (false) or renamings not containing this reference
     *                                   should be returned (true).
     * @return A list of all possible variable renamings for the given references.
     */
    private static List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> findAllRenamings(
        LLVMMergeResult newResult,
        Set<? extends LLVMHeuristicVariable> ofRefs,
        boolean instIsNewerState,
        boolean tolerateRefsWithoutPartner
    ) {
        // This will be extended for each variable, and we generate one copy per possibility:
        List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> constructedMaps =
            new LinkedList<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>>();
        // We start with the empty one:
        constructedMaps.add(new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>());
        for (LLVMHeuristicVariable ofRef : ofRefs) {
            Set<LLVMSimpleTerm> ofRefInstPartners = newResult.getRefPartners(ofRef, instIsNewerState);
            if (!tolerateRefsWithoutPartner || ofRef.isConcrete() || !ofRefInstPartners.isEmpty()) {
                List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> extendedMaps =
                    new LinkedList<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>>();
                for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> existingMap : constructedMaps) {
                    for (LLVMSimpleTerm instRef : ofRefInstPartners) {
                        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> extendedMap =
                            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>(existingMap);
                        extendedMap.put(ofRef, (LLVMHeuristicVariable)instRef);
                        extendedMaps.add(extendedMap);
                    }
                    if (ofRef.isConcrete()) {
                        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> extendedMap =
                            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>(existingMap);
                        LLVMNonMergedConstRef unmerged = ((LLVMHeuristicConstRef)ofRef).asUnmerged();
                        extendedMap.put(unmerged, unmerged);
                        extendedMaps.add(extendedMap);
                    }
                }
                constructedMaps = extendedMaps;
            }
        }
        return constructedMaps;
    }

    /**
     * @param state Some state.
     * @param rel Some relation from state.
     * @return If the relation is of the form v1 + (c * v2) <(=) 1 + b for a constant factor c > 1, two references v1
     *         and v2, and the upper bound b of an allocated area, then this method returns v2. If the relation is an
     *         equation where one side is of the form v1 + (c * v2) like above and the other side is a reference
     *         (possibly with a constant offset) associated to the area (a, b), we try to infer the biggest reference
     *         v3 such that v1 + (c * v3) <= b + 1. If we can find such a reference, we return v3. Null otherwise.
     */
    private static LLVMHeuristicVariable findArrayPattern(LLVMHeuristicState state, LLVMHeuristicRelation rel, Abortion aborter) {
        final LLVMHeuristicRelationFactory relationFactory = state.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        LLVMHeuristicTerm lhs = rel.getLhs();
        LLVMHeuristicTerm rhs = rel.getRhs();
        switch (rel.getHeuristicRelationType()) {
            case NE:
                return null;
            case EQ:
                LLVMHeuristicVariable index = LLVMHeuristicStateFactory.findArrayPattern(lhs);
                LLVMHeuristicTerm expr = rhs;
                LLVMHeuristicTerm indexSide = lhs;
                if (index == null) {
                    index = LLVMHeuristicStateFactory.findArrayPattern(rhs);
                    expr = lhs;
                    indexSide = rhs;
                }
                if (index == null) {
                    return null;
                }
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
                if (!(exprLinear.x instanceof LLVMHeuristicVariable && exprLinear.z.compareTo(BigInteger.ONE) == 0)) {
                    return null;
                }
                LLVMHeuristicVariable ref = (LLVMHeuristicVariable)exprLinear.x;
                Integer associationIndex = state.getAssociations().get(ref);
                if (associationIndex == null) {
                    return null;
                }
                LLVMHeuristicVariable upper = (LLVMHeuristicVariable)state.getAllocations().get(associationIndex).y;
                TreeSet<Pair<LLVMHeuristicVariable, BigInteger>> indexCandidates =
                    LLVMHeuristicStateFactory.computeEqualRefOffsetPairs(state, index, aborter);
                LLVMHeuristicTerm right = termFactory.add(termFactory.one(), upper);
                for (Pair<LLVMHeuristicVariable, BigInteger> candidate : indexCandidates) {
                    if (
                        state.getIntegerState().truthValueOfRelation(
                            relationFactory.lessThanEquals(
                                indexSide.substitute(Collections.singletonMap(index, candidate.x)),
                                right
                            ),
                            true,
                            aborter
                        ) == YNM.YES
                    ) {
                        return candidate.x;
                    }
                }
                return null;
            default:
                if (!(rhs instanceof LLVMHeuristicOperation)) {
                    return null;
                }
                LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhs;
                if (op.getOperation() != ArithmeticOperationType.ADD || !op.isSimple()) {
                    return null;
                }
                LLVMHeuristicVariable ref1 = (LLVMHeuristicVariable)op.getLhs();
                LLVMHeuristicVariable ref2 = (LLVMHeuristicVariable)op.getRhs();
                if (ref1.equals(termFactory.one())) {
                    for (LLVMAllocation allocation : state.getAllocations()) {
                        if (allocation.y.equals(ref2)) {
                            return LLVMHeuristicStateFactory.findArrayPattern(lhs);
                        }
                    }
                } else if (ref2.equals(termFactory.one())) {
                    for (LLVMAllocation allocation : state.getAllocations()) {
                        if (allocation.y.equals(ref1)) {
                            return LLVMHeuristicStateFactory.findArrayPattern(lhs);
                        }
                    }
                }
                return null;
        }
    }

    /**
     * @param expr Some expression.
     * @return If the expression is of the form v1 + (c * v2) for a constant factor c > 1 and two references v1 and v2,
     *         then this method returns v2. Null otherwise.
     */
    private static LLVMHeuristicVariable findArrayPattern(LLVMHeuristicTerm expr) {
        if (!(expr instanceof LLVMHeuristicOperation)) {
            return null;
        }
        LLVMHeuristicOperation op = (LLVMHeuristicOperation)expr;
        if (op.getOperation() != ArithmeticOperationType.ADD) {
            return null;
        }
        LLVMHeuristicTerm opLhs = op.getLhs();
        LLVMHeuristicTerm opRhs = op.getRhs();
        final LLVMHeuristicOperation offset;
        if (opLhs instanceof LLVMHeuristicVariable) {
            if (!(opRhs instanceof LLVMHeuristicOperation)) {
                return null;
            }
            offset = (LLVMHeuristicOperation)opRhs;
        } else if (opRhs instanceof LLVMHeuristicVariable) {
            if (!(opLhs instanceof LLVMHeuristicOperation)) {
                return null;
            }
            offset = (LLVMHeuristicOperation)opLhs;
        } else {
            return null;
        }
        if (offset.getOperation() != ArithmeticOperationType.MUL) {
            return null;
        }
        LLVMHeuristicTerm offLhs = offset.getLhs();
        LLVMHeuristicTerm offRhs = offset.getRhs();
        if (offLhs instanceof LLVMHeuristicConstRef) {
            if (
                ((LLVMHeuristicConstRef)offLhs).getIntegerValue().compareTo(BigInteger.ONE) > 0
                && offRhs instanceof LLVMHeuristicVariable
            ) {
                return (LLVMHeuristicVariable)offRhs;
            }
        } else if (offRhs instanceof LLVMHeuristicConstRef) {
            if (
                ((LLVMHeuristicConstRef)offRhs).getIntegerValue().compareTo(BigInteger.ONE) > 0
                && offLhs instanceof LLVMHeuristicVariable
            ) {
                return (LLVMHeuristicVariable)offLhs;
            }
        }
        return null;
    }

    /**
     * @param state The abstract state holding knowledge about references.
     * @param rels The relations to consider.
     * @param a A reference.
     * @param b Another reference.
     * @param offset An offset.
     * @param limit The limit for offset.
     * @return A set of references y for which the relations imply that a + d <= b for a maximal constant d with
     *         offset + d < c.
     */
    private static Set<LLVMHeuristicVariable> findBiggestBetweenWithSmallerOffsetThanLimit(
        LLVMHeuristicState state,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicVariable a,
        LLVMHeuristicVariable b,
        BigInteger offset,
        BigInteger limit,
        Abortion aborter
    ) {
        Set<LLVMHeuristicVariable> res = new LinkedHashSet<LLVMHeuristicVariable>();
        for (LLVMHeuristicRelation rel : rels.getEquations()) {
            aborter.checkAbortion();
            Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> pattern = rel.toOffByConstantPattern();
            if (pattern == null) {
                continue;
            }
            LLVMHeuristicVariable next;
            BigInteger nextOff;
            if (pattern.x.equals(a)) {
                next = pattern.y;
                nextOff = pattern.z;
            } else if (pattern.y.equals(a)) {
                next = pattern.x;
                nextOff = pattern.z.negate();
            } else {
                next = null;
                nextOff = null;
            }
            if (nextOff == null || nextOff.compareTo(BigInteger.ZERO) < 0) {
                continue;
            }
            BigInteger totalOffset = offset.add(nextOff);
            if (totalOffset.compareTo(limit) > 0) {
                continue;
            }
            if (next.equals(b)) {
                return Collections.<LLVMHeuristicVariable>singleton(b);
            }
            Set<LLVMHeuristicVariable> bigger =
                LLVMHeuristicStateFactory.findBiggestBetweenWithSmallerOffsetThanLimit(
                    state,
                    rels,
                    next,
                    b,
                    totalOffset,
                    limit,
                    aborter
                );
            if (!bigger.isEmpty()) {
                res.addAll(bigger);
                continue;
            }
            if (
                state.getIntegerState().truthValueOfRelation(
                    rels,
                    next,
                    LLVMHeuristicRelationType.LE,
                    b,
                    true,
                    aborter
                ) == YNM.YES
            ) {
                res.add(next);
            }
        }
        return res;
    }
    
    private static void findReferencePairsInRelations(
    		LLVMMergeResult newResult,
    		boolean instIsNewerState,
    		boolean aggressive,
    		boolean fastConvergence,
    		Abortion aborter)
    throws TooExpensiveException {
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicRelationSet ofRelations = new LLVMHeuristicRelationSet(ofState.getRelations());
        LLVMHeuristicRelationSet instRelations = new LLVMHeuristicRelationSet(instState.getRelations());
        boolean changed = true;
        while (changed) {
            aborter.checkAbortion();
            changed = false;
            outer: for (LLVMHeuristicRelation ofRel : ofRelations) {
                if (!ofRel.isEquation() || !ofRel.getLhs().isLinear() || !ofRel.getRhs().isLinear()) continue;
                LLVMHeuristicVarRef newOfRef = null;
                boolean foundNewOfRef = false;
                for (LLVMHeuristicVariable ofVar : ofRel.getVariables()) {
                    if (!(ofVar instanceof LLVMHeuristicVarRef)) continue;
                    Set<LLVMSimpleTerm> instCandidates = newResult.getRefPartners(ofVar, instIsNewerState);
                    if (instCandidates.isEmpty()) {
                        for (LLVMMemoryInvariant inv : newResult.getOfState(instIsNewerState).getMemory().values()) {
                            if (inv instanceof LLVMSimpleMemoryInvariant && ((LLVMSimpleMemoryInvariant)inv).getPointedToValue().equals(ofVar)) {
                                continue outer;
                            }
                        }
                        if (foundNewOfRef) {
                            continue outer;
                        } else {
                            newOfRef = (LLVMHeuristicVarRef) ofVar;
                            foundNewOfRef = true;
                        }
                    }
                }
                if (!foundNewOfRef || ofRel.solveFor(newOfRef) == null) continue outer;
                LLVMHeuristicTerm ofTerm = ofRel.solveFor(newOfRef).x;
                List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> varMaps =
                    LLVMHeuristicStateFactory.findAllRenamings(newResult, ofTerm.getVariables(), instIsNewerState, false);
                for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap : varMaps) {
                    for (LLVMHeuristicRelation instRel : instRelations) {
                        if (!instRel.isEquation() || !instRel.getLhs().isLinear() || !instRel.getRhs().isLinear()) continue;
                        for (LLVMHeuristicVariable instVar : instRel.getVariables()) {
                            if (!(instVar instanceof LLVMHeuristicVarRef) || instRel.solveFor(instVar) == null) continue;
                            LLVMHeuristicTerm instTerm = instRel.solveFor(instVar).x;
                            if (instTerm.equals(ofTerm.applySubstitution(varMap))) {
                                LLVMHeuristicStateFactory.mergeReferences(
                                    newResult,
                                    instVar,
                                    newOfRef,
                                    null,
                                    instIsNewerState,
                                    aggressive,
                                    fastConvergence
                                );
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * @param state Some abstract LLVM state.
     * @param index The index of an allocation within the specified state.
     * @return The index of the stack frame in which the allocation has been allocated. A negative value indicated that
     *         the allocation has not been made within the stack.
     */
    private static int getStackFrameIndex(LLVMAbstractState state, int index) {
        if (state.getAllocatedByMallocIndices().contains(index)) {
            return LLVMMergeResult.ALLOCATION_BY_MALLOC;
        }
        if (state.getAllocatedInCurrentFunctionFrameIndices().contains(index)) {
            return state.getCallStack().size();
        }
        int res = 0;
        for (LLVMReturnInformation info : state.getCallStack()) {
            if (info.getAllocationsInFunction().contains(index)) {
                return res;
            }
            res++;
        }
        throw new IllegalStateException("Found an allocation which has never been allocated!");
    }
    
    private static ImmutableList<LLVMType> getStructTypes(Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct) {
        List<LLVMType> structTypes = new LinkedList<LLVMType>();
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : struct) {
            structTypes.add(triple.y);
        }
        return ImmutableCreator.create(structTypes);
    }

    /**
     * Tries to guess relations that hold in both states but are not explicitly contained in either of the states,
     * using the computed program relations.
     * @param newResult The generalization result under construction.
     * @param instIsNewerState Indicates if the instance state is the newer state.
     */
    private static void guessRelations(LLVMMergeResult newResult, boolean instIsNewerState, Abortion aborter) {
        LLVMHeuristicState mergedState = (LLVMHeuristicState)newResult.getGeneralizedState();
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicRelationSet res = new LLVMHeuristicRelationSet();
        ImmutableSet<LLVMLiteralRelation> litRelations = instState.getModule().getProgramLiteralRelations();
        final LLVMHeuristicRelationFactory relationFactory = mergedState.getRelationFactory();
        for (LLVMLiteralRelation rel : litRelations) {
            if (rel.holdsIn(instState) && rel.holdsIn(ofState)) {
                Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef =  new LinkedHashMap<>();
                for (LLVMVariableLiteral progVar : rel.getVariables()) {
                    LLVMHeuristicVariable refForProgVar = mergedState.getSimpleTermForLiteral(progVar);
                    if (!refForProgVar.isConcrete()) {
                        varToRef.put(progVar, mergedState.getSimpleTermForLiteral(progVar));
                    }
                }
                if (!varToRef.isEmpty()) {
                    LLVMHeuristicRelation newRel = rel.transformToLLVMHeuristicRelation(varToRef, relationFactory);
                    if (newRel != null && !mergedState.getRelations().contains(newRel)) {
                        res.add(newRel);
                    }
                }
            }
        }
//        ImmutableSet<LLVMRelation> refRelations = instState.getModule().getProgramReferenceRelations();
//        for (LLVMRelation rel : refRelations) {
//            for (LLVMAllocation allocArea : instState.getAllocations()) {
//                // TODO better heuristic
//                for (LLVMHeuristicVariable sizeRef : instState.getValues().keySet()) {
//                    LLVMHeuristicRelation instRel =
//                        ((LLVMHeuristicRelation)rel).applySubstitution(
//                            LLVMHeuristicVarRef.startOfAllocatedArea, (LLVMHeuristicTerm)allocArea.x
//                        ).applySubstitution(
//                            LLVMHeuristicVarRef.endOfAllocatedArea, (LLVMHeuristicTerm)allocArea.y
//                        ).applySubstitution(
//                            LLVMHeuristicVarRef.sizeOfAllocatedArea, sizeRef
//                        );
//                    List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> varMaps =
//                        LLVMHeuristicStateFactory.findAllRenamings(
//                            newResult,
//                            instRel.getVariables(),
//                            instIsNewerState,
//                            false
//                        );
//                    for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap : varMaps) {
//                        LLVMHeuristicRelation ofRel = instRel.applySubstitution(varMap);
//                        if (instState.checkRelation(instRel, aborter).x && ofState.checkRelation(ofRel, aborter).x) {
//                            // Build image of this in the merged state, add:
//                            LLVMHeuristicRelation newRel =
//                                instRel.applySubstitution(
//                                    LLVMHeuristicStateFactory.buildMergeSubstitution(newResult, varMap, instIsNewerState)
//                                );
//                            if (newRel != null && !mergedState.getRelations().contains(newRel)) {
//                                res.add(newRel);
//                            }
//                        }
//                    }
//                }
//            }
//        }
        newResult.setGeneralizedState(mergedState.addRelations(res, aborter).x);
    }

    /**
     * Adds suitably generalized pairs of references to the allocation areas. It tries to find a bijection on subsets
     * of the allocated areas in both inst- and of-state. Variables must already have been handled before calling this
     * method.
     * @param newResult The generalization result under construction.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @throws TooExpensiveException If this got too expensive.
     * @throws MemoryLeakException If information about mallocated memory is lost.
     */
    private static void handleAllocations(LLVMMergeResult newResult, boolean aggressive, boolean fastConvergence) throws TooExpensiveException, MemoryLeakException {
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(true);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(true);
        IntegerType pointerType =
            instState.getModule().getPointerType(instState.getStrategyParamters().useBoundedIntegers);
        ImmutableList<LLVMAllocation> instAlloc = instState.getAllocations();
        ImmutableList<LLVMAllocation> ofAlloc = ofState.getAllocations();
        ImmutableMap<LLVMHeuristicVariable, Integer> instMem = instState.getAssociations();
        ImmutableMap<LLVMHeuristicVariable, Integer> ofMem = ofState.getAssociations();
        for (int ofIndex = 0; ofIndex < ofAlloc.size(); ofIndex++) {
            LLVMAllocation ofArea = ofAlloc.get(ofIndex);
            Set<LLVMSimpleTerm> firstOfBorderInstPartners = newResult.getRefPartners(ofArea.x, true);
            Set<LLVMSimpleTerm> secondOfBorderInstPartners = newResult.getRefPartners(ofArea.y, true);
            boolean renameX = firstOfBorderInstPartners.isEmpty();
            boolean renameY = secondOfBorderInstPartners.isEmpty();
            if (renameX || renameY) {
                if (!renameX || !renameY) {
                    // exactly one border is not referenced by a variable
                    Set<LLVMSimpleTerm> renamedInstPartners =
                        renameX ? secondOfBorderInstPartners : firstOfBorderInstPartners;
                    LLVMHeuristicVariable unrenamedOfBorder = (LLVMHeuristicVariable)(renameX ? ofArea.x : ofArea.y);
                    for (LLVMSimpleTerm renamedInstBorder : renamedInstPartners) {
                        // this point must be reached at least once
                        for (int instIndex = 0; instIndex < instAlloc.size(); instIndex++) {
                            LLVMAllocation instArea = instAlloc.get(instIndex);
                            LLVMHeuristicVariable existingInstBorder =
                                (LLVMHeuristicVariable)(renameX ? instArea.y : instArea.x);
                            if (existingInstBorder.equals(renamedInstBorder)) {
                                // found an area with the renamed reference in the same position
                                int instStackFrame = LLVMHeuristicStateFactory.getStackFrameIndex(instState, instIndex);
                                int ofStackFrame = LLVMHeuristicStateFactory.getStackFrameIndex(ofState, ofIndex);
                                if (instStackFrame == ofStackFrame) {
                                    // and the area is within the same stack frame in both states
                                    // => merge other reference and match areas
                                    if (newResult.mergeAreas(instIndex, ofIndex, instStackFrame, true)) {
                                        LLVMHeuristicStateFactory.mergeReferences(
                                            newResult,
                                            (LLVMHeuristicVariable)(renameX ? instArea.x : instArea.y),
                                            unrenamedOfBorder,
                                            pointerType,
                                            true,
                                            aggressive,
                                            fastConvergence
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                // both borders are referenced by variables
                for (LLVMSimpleTerm firstInstBorder : firstOfBorderInstPartners) {
                    for (LLVMSimpleTerm secondInstBorder : secondOfBorderInstPartners) {
                        // this point must be reached at least once
                        LLVMAllocation instRenamedArea = new LLVMAllocation(firstInstBorder, secondInstBorder);
                        if (instAlloc.contains(instRenamedArea)) {
                            // renamed area exists - just match them
                            if (
                                !newResult.mergeAreas(
                                    instAlloc.indexOf(instRenamedArea),
                                    ofIndex,
                                    LLVMHeuristicStateFactory.getStackFrameIndex(ofState, ofIndex),
                                    true
                                )
                            ) {
                                throw new IllegalStateException("Matching renamed areas failed!");
                            }
                        }
                    }
                }
            }
            // we can still look for connections over associated references
            for (Map.Entry<LLVMHeuristicVariable, Integer> ofAssociation : ofMem.entrySet()) {
                if (ofIndex == ofAssociation.getValue()) {
                    for (LLVMSimpleTerm instAssRef : newResult.getRefPartners(ofAssociation.getKey(), true)) {
                        if (instMem.containsKey(instAssRef)) {
                            // we found a connection
                            int instIndex = instMem.get(instAssRef);
                            int instStackFrame = LLVMHeuristicStateFactory.getStackFrameIndex(instState, instIndex);
                            int ofStackFrame = LLVMHeuristicStateFactory.getStackFrameIndex(ofState, ofIndex);
                            if (instStackFrame == ofStackFrame) {
                                // and the area is within the same stack frame in both states
                                // => merge border references and areas
                                LLVMAllocation instArea = instAlloc.get(instIndex);
                                if (newResult.mergeAreas(instIndex, ofIndex, instStackFrame, true)) {
                                    LLVMHeuristicStateFactory.mergeReferences(
                                        newResult,
                                        (LLVMHeuristicVariable)instArea.x,
                                        (LLVMHeuristicVariable)ofArea.x,
                                        pointerType,
                                        true,
                                        aggressive,
                                        fastConvergence
                                    );
                                    LLVMHeuristicStateFactory.mergeReferences(
                                        newResult,
                                        (LLVMHeuristicVariable)instArea.y,
                                        (LLVMHeuristicVariable)ofArea.y,
                                        pointerType,
                                        true,
                                        aggressive,
                                        fastConvergence
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        // after we tried to find connections by references, we might additionally just have unreferenced equal areas
        Map<Integer, Integer> bijection = newResult.getAllocationBijection();
        for (int ofIndex = 0; ofIndex < ofAlloc.size(); ofIndex++) {
            if (bijection.containsValue(ofIndex)) {
                // this area has already been merged
                continue;
            }
            LLVMAllocation ofArea = ofAlloc.get(ofIndex);
            for (int instIndex = 0; instIndex < instAlloc.size(); instIndex++) {
                if (bijection.containsKey(instIndex)) {
                    // this area has already been merged
                    continue;
                }
                LLVMAllocation instArea = instAlloc.get(instIndex);
                if (ofArea.equals(instArea)) {
                    // found equal unmerged areas
                    int instStackFrame = LLVMHeuristicStateFactory.getStackFrameIndex(instState, instIndex);
                    int ofStackFrame = LLVMHeuristicStateFactory.getStackFrameIndex(ofState, ofIndex);
                    if (instStackFrame == ofStackFrame) {
                        // try to merge them
                        if (newResult.mergeAreas(instIndex, ofIndex, instStackFrame, true)) {
                            LLVMHeuristicStateFactory.mergeReferences(
                                newResult,
                                (LLVMHeuristicVariable)instArea.x,
                                (LLVMHeuristicVariable)ofArea.x,
                                pointerType,
                                true,
                                aggressive,
                                fastConvergence
                            );
                            LLVMHeuristicStateFactory.mergeReferences(
                                newResult,
                                (LLVMHeuristicVariable)instArea.y,
                                (LLVMHeuristicVariable)ofArea.y,
                                pointerType,
                                true,
                                aggressive,
                                fastConvergence
                            );
                        }
                    }
                }
            }
        }
        // now all surviving references should be renamed somehow
        List<LLVMAllocation> newAllocs = new ArrayList<LLVMAllocation>(newResult.getGeneralizedState().getAllocations());
        for (int i = instAlloc.size() - newResult.getNumberOfMergedAreas(); i > 0; i--) {
            newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, true);
        }
        for (int i = ofAlloc.size() - newResult.getNumberOfMergedAreas(); i > 0; i--) {
            newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, false);
        }
        TreeSet<Integer> newFrameIndices = new TreeSet<Integer>();
        List<TreeSet<Integer>> stackAllocationIndices = new ArrayList<>(instState.getCallStack().size());
        for(int stackFrame = 0; stackFrame < instState.getCallStack().size(); stackFrame++) {
        	stackAllocationIndices.add(new TreeSet<>());
        }
        
        TreeSet<Integer> newMallocIndices = new TreeSet<Integer>();
        for (int mergedIndex = 0; mergedIndex < newResult.getNumberOfMergedAreas(); mergedIndex++) {
            AllocationMapping indices = newResult.getAllocationMappingForMergedIndex(mergedIndex, true);
            if (Globals.useAssertions) {
                assert (indices != null) : "Found merged index without source indices!";
            }
            LLVMAllocation instArea = instAlloc.get(indices.x);
            LLVMAllocation ofArea = ofAlloc.get(indices.y);
            newAllocs.add(
                new LLVMAllocation(
                    newResult.getMergedRef(instArea.x, ofArea.x, true),
                    newResult.getMergedRef(instArea.y, ofArea.y, true)
                )
            );
            if (indices.z == instState.getCallStack().size()) {
                newFrameIndices.add(newAllocs.size()-1);
            } else if (indices.z == LLVMMergeResult.ALLOCATION_BY_MALLOC) {
                newMallocIndices.add(newAllocs.size()-1);
            } else {
            	//allocation in lower stack frame
            	TreeSet<Integer> lowerFrameIndices = stackAllocationIndices.get(indices.z);
            	lowerFrameIndices.add(newAllocs.size()-1);
            	
            }
        }
        // Check whether a reference to a mallocated area gets lost
        if (instState.getStrategyParamters().proveFreeOfMemoryLeaks) {
            for (int index : instState.getAllocatedByMallocIndices()) {
                if (newResult.getAllocationPartner(index, true) == -1) {
                    throw new MemoryLeakException("Probably lost references to malloced memory!");
                }
            }
        }
        newResult.setGeneralizedState(
            newResult.getGeneralizedState().setAllocatedMemoryForAllocaAndMalloc(
                newAllocs,
                newFrameIndices,
                newMallocIndices
            )
        );
        
        //Update stack of generalized state with new stack allocation indices
        Deque<LLVMReturnInformation> newCallStack = new ArrayDeque<>(stackAllocationIndices.size());
        int frameIndex = 0;
        for(LLVMReturnInformation oldStackFrame : newResult.getGeneralizedState().getCallStack()) {
        	LLVMReturnInformation updatedFrame = new LLVMReturnInformation(
        			oldStackFrame.getProgramVariables(),
        			oldStackFrame.getProgPos(), 
        			ImmutableCreator.create(stackAllocationIndices.get(frameIndex)));
        	newCallStack.add(updatedFrame);
        	frameIndex++;
        }
        newResult.setGeneralizedState(newResult.getGeneralizedState().setCallStack(newCallStack));
    }

    /**
     * Special case: we have a relation v1 + (c * v2) <(=) expr for a constant factor c with |c| != 1 in
     * the merged state. Then v2 is probably an index for an array. Try to find other references which are
     * bounded by the index in some direction and add the corresponding relations.
     * @param newResult The generalization result currently under construction.
     */
    private static void handleArrayIndices(LLVMMergeResult newResult, Abortion aborter) {
        LLVMHeuristicState mergedState = (LLVMHeuristicState)newResult.getGeneralizedState();
        final boolean useBoundedIntegers = mergedState.getStrategyParamters().useBoundedIntegers;
        LLVMHeuristicState newState = (LLVMHeuristicState)newResult.getNewerState();
        LLVMHeuristicState oldState = (LLVMHeuristicState)newResult.getOlderState();
        final LLVMHeuristicRelationFactory relationFactory = mergedState.getRelationFactory();
        LLVMHeuristicRelationSet res = new LLVMHeuristicRelationSet();
        ImmutableSet<LLVMHeuristicRelation> newRels = newState.getRelations();
        ImmutableSet<LLVMHeuristicRelation> oldRels = oldState.getRelations();
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVars = newState.getProgramVariables();
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> oldVars = oldState.getProgramVariables();
        ImmutableMap<LLVMMemoryRange,LLVMMemoryInvariant> newHeap = newState.getMemory();
        ImmutableMap<LLVMMemoryRange,LLVMMemoryInvariant> oldHeap = oldState.getMemory();
        Set<LLVMHeuristicVariable> foundMergedIndices = new LinkedHashSet<LLVMHeuristicVariable>();
        for (LLVMHeuristicRelation mergedRel : mergedState.getRelations()) {
            aborter.checkAbortion();
            LLVMHeuristicVariable mergedIndex = LLVMHeuristicStateFactory.findArrayPattern(mergedState, mergedRel, aborter);
            if (mergedIndex == null || foundMergedIndices.contains(mergedIndex)) {
                continue;
            }
            foundMergedIndices.add(mergedIndex);
            for (
                Map.Entry<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> entry :
                    newResult.getRefMapping().entrySet()
            ) {
                if (!entry.getValue().equals(mergedIndex)) {
                    continue;
                }
                Pair<LLVMSimpleTerm, LLVMSimpleTerm> indices = entry.getKey();
                boolean ok = false;
                for (LLVMHeuristicRelation newRel : newRels) {
                    LLVMHeuristicVariable newIndex = LLVMHeuristicStateFactory.findArrayPattern(newState, newRel, aborter);
                    if (newIndex != null && newIndex.equals(indices.x)) {
                        ok = true;
                        break;
                    }
                }
                if (!ok) {
                    continue;
                }
                ok = false;
                for (LLVMHeuristicRelation oldRel : oldRels) {
                    LLVMHeuristicVariable oldIndex = LLVMHeuristicStateFactory.findArrayPattern(oldState, oldRel, aborter);
                    if (oldIndex != null && oldIndex.equals(indices.y)) {
                        ok = true;
                        break;
                    }
                }
                if (!ok) {
                    continue;
                }
                /*
                 * now we have the index references in each state - compare variables and their dereferencings to find
                 * pairs of references which are bounded by the indices
                 */
                // holds pairs of pairs of references and types in the new/old state for the same variables or
                // dereferencings
                Set<DerefVarMatch> sameVarOrDeref = new LinkedHashSet<DerefVarMatch>();
                Set<DerefVarMatch> newSameVarOrDeref = new LinkedHashSet<DerefVarMatch>();
                for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newEntry : newVars.entrySet()) {
                    ImmutablePair<LLVMSymbolicVariable, LLVMType> oldPair = oldVars.get(newEntry.getKey());
                    if (oldPair == null) {
                        continue;
                    }
                    boolean unsigned = false;
                    if (useBoundedIntegers) {
                        unsigned = newState.getModule().getAddressesToUnsignedBitvectorVariables().contains(newEntry.getKey());
                    }
                    newSameVarOrDeref.add(new DerefVarMatch(newEntry.getValue(), oldPair, unsigned));
                }
                while (!newSameVarOrDeref.isEmpty()) {
                    aborter.checkAbortion();
                    sameVarOrDeref.addAll(newSameVarOrDeref);
                    Set<DerefVarMatch> oldSameVarOrDeref = new LinkedHashSet<DerefVarMatch>(newSameVarOrDeref);
                    newSameVarOrDeref.clear();
                    for (DerefVarMatch match : oldSameVarOrDeref) {
                        LLVMHeuristicVariable newRef = (LLVMHeuristicVariable)match.x.x;
                        LLVMHeuristicVariable oldRef = (LLVMHeuristicVariable)match.y.x;
                        LLVMType newType = match.x.y;
                        if (Globals.useAssertions) {
                            assert (newType.equals(match.y.y)) :
                                "Found different types for variable/dereferencing match!";
                        }
                        // first check whether there are further dereferencings
                        if (newType.isPointerType()){
                            LLVMType targetType = newType.getThisAsPointerType().getTargetType();
                            LLVMMemoryRange newHeapAccess = new LLVMMemoryRange(newRef,newRef, targetType, match.z);
                            LLVMMemoryRange oldHeapAccess = new LLVMMemoryRange(oldRef,oldRef, targetType, match.z);
                            if (newHeap.containsKey(newHeapAccess) && oldHeap.containsKey(oldHeapAccess)) {
                                newSameVarOrDeref.add(
                                    new DerefVarMatch(
                                        new ImmutablePair<LLVMSimpleTerm, LLVMType>(
                                            ((LLVMSimpleMemoryInvariant)newHeap.get(newHeapAccess)).getPointedToValue(),
                                            targetType
                                        ),
                                        new ImmutablePair<LLVMSimpleTerm, LLVMType>(
                                            ((LLVMSimpleMemoryInvariant)oldHeap.get(oldHeapAccess)).getPointedToValue(),
                                            targetType
                                        ),
                                        match.z
                                    )
                                );
                            }
                        }
                        AbstractBoundedInt newVal = newState.getValue(newRef).getThisAsAbstractBoundedInt();
                        AbstractBoundedInt oldVal = oldState.getValue(oldRef).getThisAsAbstractBoundedInt();
                        LLVMHeuristicVariable mergedRef =
                            (LLVMHeuristicVariable)newResult.getMergedRef(newRef, oldRef, true);
                        if (
                            !LLVMHeuristicStateFactory.candidateForIndexRelation(
                                newState,
                                oldState,
                                newRef,
                                oldRef,
                                indices,
                                newVal,
                                oldVal,
                                mergedRef,
                                mergedIndex,
                                aborter
                            )
                        ) {
                            continue;
                        }
                        YNM lt =
                            newState.getIntegerState().truthValueOfRelation(
                                newRef,
                                LLVMHeuristicRelationType.LT,
                                (LLVMHeuristicTerm)indices.x,
                                true,
                                aborter
                            );
                        switch (lt) {
                            case YES:
                                if (
                                    oldState.getIntegerState().truthValueOfRelation(
                                        oldRef,
                                        LLVMHeuristicRelationType.LT,
                                        (LLVMHeuristicTerm)indices.y,
                                        true,
                                        aborter
                                    ) == YNM.YES
                                ) {
                                    // both refs are lt index
                                    res.add(relationFactory.lessThan(mergedRef, mergedIndex));
                                } else if (
                                    oldState.getIntegerState().truthValueOfRelation(
                                        oldRef,
                                        LLVMHeuristicRelationType.LE,
                                        (LLVMHeuristicTerm)indices.y,
                                        true,
                                        aborter
                                    ) == YNM.YES
                                ) {
                                    // both refs are at least le index
                                    res.add(relationFactory.lessThanEquals(mergedRef, mergedIndex));
                                }
                                // else do nothing
                                break;
                            case NO:
                                if (
                                    newState.getIntegerState().truthValueOfRelation(
                                        (LLVMHeuristicTerm)indices.x,
                                        LLVMHeuristicRelationType.LT,
                                        newRef,
                                        true,
                                        aborter
                                    ) == YNM.YES
                                ) {
                                    if (
                                        oldState.getIntegerState().truthValueOfRelation(
                                            (LLVMHeuristicTerm)indices.y,
                                            LLVMHeuristicRelationType.LT,
                                            oldRef,
                                            true,
                                            aborter
                                        ) == YNM.YES
                                    ) {
                                        // both refs are gt index
                                        res.add(relationFactory.lessThan(mergedIndex, mergedRef));
                                    } else if (
                                        oldState.getIntegerState().truthValueOfRelation(
                                            (LLVMHeuristicTerm)indices.y,
                                            LLVMHeuristicRelationType.LE,
                                            oldRef,
                                            true,
                                            aborter
                                        ) == YNM.YES
                                    ) {
                                        // both refs are at least ge index
                                        res.add(relationFactory.lessThanEquals(mergedIndex, mergedRef));
                                    }
                                    // else do nothing
                                } else if (
                                    oldState.getIntegerState().truthValueOfRelation(
                                        (LLVMHeuristicTerm)indices.y,
                                        LLVMHeuristicRelationType.LE,
                                        oldRef,
                                        true,
                                        aborter
                                    ) == YNM.YES
                                ) {
                                    // both refs are at least ge index
                                    res.add(relationFactory.lessThanEquals(mergedIndex, mergedRef));
                                }
                                // else do nothing
                                break;
                            default:
                                // we know that newRef cannot be proven to be lt or ge index
                                YNM le =
                                    newState.getIntegerState().truthValueOfRelation(
                                        newRef,
                                        LLVMHeuristicRelationType.LE,
                                        (LLVMHeuristicTerm)indices.x,
                                        true,
                                        aborter
                                    );
                                switch (le) {
                                    case YES:
                                        // newRef <= index
                                        if (
                                            oldState.getIntegerState().truthValueOfRelation(
                                                oldRef,
                                                LLVMHeuristicRelationType.LE,
                                                (LLVMHeuristicTerm)indices.y,
                                                true,
                                                aborter
                                            ) == YNM.YES
                                        ) {
                                            // both refs are at least le index
                                            res.add(relationFactory.lessThanEquals(mergedRef, mergedIndex));
                                        }
                                        break;
                                    case NO:
                                        throw new IllegalStateException("We could not prove NO for LT, but NO for LE!");
                                    default:
                                        // do nothing
                                }
                        }
                    }
                    newSameVarOrDeref.removeAll(sameVarOrDeref);
                }
            }
        }
        newResult.setGeneralizedState(mergedState.addRelations(res, aborter).x);
    }

    /**
     * Adds suitably general values for all associations. Variables, allocated areas, and the heap must already have
     * been handled before calling this method.
     * @param newResult the generalization result currently constructed
     * @param instIsNewerState indicates if the instance state is the newer state
     * @throws TooExpensiveException if this got too expensive
     */
    private static void handleAssociations(LLVMMergeResult newResult, boolean instIsNewerState)
    throws TooExpensiveException {
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState genState = (LLVMHeuristicState)newResult.getGeneralizedState();
        ImmutableMap<LLVMHeuristicVariable, Integer> instAssocs = instState.getAssociations();
        ImmutableMap<LLVMHeuristicVariable, Integer> ofAssocs = ofState.getAssociations();
        ImmutableMap<LLVMHeuristicVariable, BigInteger> instAssocOffsets = instState.getAssociationOffsets();
        ImmutableMap<LLVMHeuristicVariable, BigInteger> ofAssocOffsets = ofState.getAssociationOffsets();
        Map<LLVMHeuristicVariable, Integer> newAssocs =
            new LinkedHashMap<LLVMHeuristicVariable, Integer>(genState.getAssociations());
        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets =
            new LinkedHashMap<LLVMHeuristicVariable, BigInteger>(genState.getAssociationOffsets());
        for (Map.Entry<LLVMHeuristicVariable, Integer> ofAssociation : ofAssocs.entrySet()) {
            int ofIndex = ofAssociation.getValue();
            int instIndex = newResult.getAllocationPartner(ofIndex, instIsNewerState);
            if (instIndex > -1) {
                LLVMHeuristicVariable ofRef = ofAssociation.getKey();
                Set<LLVMSimpleTerm> instPartners = newResult.getRefPartners(ofRef, instIsNewerState);
                if (instPartners.isEmpty()) {
                    // if we have no renaming, this reference is not used anymore
                    newResult.addCost(LLVMCost.LOST_ASSOCIATED_REF, !instIsNewerState);
                } else {
                    for (LLVMSimpleTerm instRef : instPartners) {
                        if (!instAssocs.containsKey(instRef) || instIndex != instAssocs.get(instRef)) {
                            // these are costs for the of-state, since we had the association there, but not in the
                            // merge-state
                            newResult.addCost(LLVMCost.LOST_ASSOCIATED_REF, !instIsNewerState);
                        } else {
                            LLVMHeuristicVariable mergedRef =
                                (LLVMHeuristicVariable)newResult.getMergedRef(instRef, ofRef, instIsNewerState);
                            newAssocs.put(
                                mergedRef,
                                newResult.getMergedArea(instIndex, ofIndex, instIsNewerState)
                            );
                            BigInteger instOffset = instAssocOffsets.get(instRef);
                            BigInteger ofOffset = ofAssocOffsets.get(ofRef);
                            BigInteger mergedOffset = ofOffset;
                            if (instOffset.compareTo(ofOffset) < 0) {
                                // in the of state, we had more offset
                                newResult.addCost(LLVMCost.LESS_ASSOCIATION_OFFSET, !instIsNewerState);
                                mergedOffset = instOffset;
                            } else if (instOffset.compareTo(ofOffset) > 0) {
                                // in the inst state, we had more offset
                                newResult.addCost(LLVMCost.LESS_ASSOCIATION_OFFSET, instIsNewerState);
                            }
                            newAssocOffsets.put(mergedRef, mergedOffset);
                        }
                    }
                }
            } else {
                // these are costs for the of-state, since we had the association there, but not in the merge-state
                newResult.addCost(LLVMCost.LOST_ASSOCIATED_REF, !instIsNewerState);
            }
        }
        newResult.setGeneralizedState(
            ((LLVMHeuristicState)newResult.getGeneralizedState()).setAssociations(newAssocs, newAssocOffsets)
        );
    }

    /**
     * Checks that the call stacks are equal after merging.
     * We already know that the call stacks have the same size (otherwise they would not be in the set of merge
     * candidates).
     * @param newResult The generalization result under construction.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @throws TooExpensiveException If the call stacks are not equal after merging.
     */
    private static void handleCallStacks(LLVMMergeResult newResult, boolean aggressive, boolean fastConvergence) throws TooExpensiveException {
        Deque<LLVMReturnInformation> genCallStack = new ArrayDeque<LLVMReturnInformation>();
        Iterator<LLVMReturnInformation> instIt = newResult.getNewerState().getCallStack().iterator();
        Iterator<LLVMReturnInformation> ofIt = newResult.getOlderState().getCallStack().iterator();
        // it suffices to ask only one iterator
        while (instIt.hasNext()) {
            LLVMReturnInformation instInf = instIt.next();
            LLVMReturnInformation ofInf = ofIt.next();
            if (
                !(
                    instInf.getProgPos().equals(ofInf.getProgPos())
                    && (aggressive || instInf.getAllocationsInFunction().equals(ofInf.getAllocationsInFunction()) )
                )
            ) {
                throw new TooExpensiveException("Call stacks not at the same position!");
            }
            Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> genVarFunc =
                new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>();
            LLVMHeuristicStateFactory.handleVariableFunctionInCallStack(
                newResult,
                genVarFunc,
                instInf.getProgramVariables(),
                ofInf.getProgramVariables(),
                true,
                aggressive,
                fastConvergence
            );
            LLVMHeuristicStateFactory.handleVariableFunctionInCallStack(
                newResult,
                genVarFunc,
                instInf.getProgramVariables(),
                ofInf.getProgramVariables(),
                false,
                aggressive,
                fastConvergence
            );
            genCallStack.add(
                new LLVMReturnInformation(
                    ImmutableCreator.create(genVarFunc),
                    instInf.getProgPos(),
                    instInf.getAllocationsInFunction()
                )
            );
        }
        newResult.setGeneralizedState(
            newResult.getGeneralizedState().setCallStack(ImmutableCreator.create(genCallStack))
        );
    }

    /**
     * Tries to detect common distances between variables in both states, such that these common distances are
     * different in the two states. More precisely, let the first state contain the pairwise distinct variables v1_1,
     * v1_2, v1_3, and v1_4 and the second state contain the pairwise distinct variables v2_1, v2_2, v2_3, and v2_4
     * such that v1_i is merged with v2_i and
     * v1_1 = v1_2 + c1
     * v1_3 = v1_4 + c1
     * v2_1 = v2_2 + c2
     * v2_3 = v2_4 + c2
     * with c1 != c2 holds for two constants c1 and c2. Moreover, we know some directed inequalities
     * v1_1 + v1_4 directedInequality expr1
     * v2_1 + v2_4 directedInequality expr2
     * (case a)
     * or
     * v1_2 + v1_3 directedInequality expr1
     * v2_3 + v2_3 directedInequality expr2
     * (case b)
     * such that all references in expr1 and expr2 are suitably merged together to exprMerged.
     * Then we add the directed inequality
     * v1_2/v2_2 + v1_3/v2_3 directedInequality exprMerged (case a) or
     * v1_1/v2_1 + v1_4/v2_4 directedInequality exprMerged (case b)
     * to the merged state.
     * TODO For now, expr1 and expr2 are restricted to be references (possibly with offset) to avoid a relation
     * explosion. Check whether there are cases where more inference is helpful.
     * @param newResult The merge result under construction.
     * @param newOffsets The offset maps for the newer state. Entries c -> {(x, y),...} in the CommonOffsetMap
     *                   represent the knowledge x = y + c. Entries x -> {(y, c),...} in the OffsetMap also represent
     *                   the knowledge x = y + c.
     * @param oldOffsets The offset maps for the older state.
     */
    private static void handleChangingCommonDistances(
        LLVMMergeResult newResult,
        Pair<LLVMOffsetMap, LLVMCommonOffsetMap> newOffsets,
        Pair<LLVMOffsetMap, LLVMCommonOffsetMap> oldOffsets,
        Abortion aborter
    ) {
        LLVMHeuristicState newState = (LLVMHeuristicState)newResult.getNewerState();
        LLVMHeuristicState oldState = (LLVMHeuristicState)newResult.getOlderState();
        final LLVMHeuristicRelationFactory relationFactory = newState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        LLVMHeuristicRelationSet newRels = new LLVMHeuristicRelationSet(newState.getRelations());
        LLVMHeuristicRelationSet oldRels = new LLVMHeuristicRelationSet(oldState.getRelations());
        LLVMHeuristicRelationSet newSuitableDirectedInequalities = new LLVMHeuristicRelationSet();
        LLVMHeuristicRelationSet oldSuitableDirectedInequalities = new LLVMHeuristicRelationSet();
        for (LLVMHeuristicRelation rel : newRels.getDirectedInequalities()) {
            aborter.checkAbortion();
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs.isSumOfTwoDifferentVariables() && rhs.getVariables(false).size() == 1) {
                newSuitableDirectedInequalities.add(rel);
                for (LLVMHeuristicRelation otherRel : newRels.getDirectedInequalities()) {
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherRhsLinear = otherRel.getRhs().toLinear();
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear = otherRel.getLhs().toLinear();
                    if (
                        !(
                            otherRhsLinear.x instanceof LLVMHeuristicVarRef
                            && otherLhsLinear.x instanceof LLVMHeuristicVarRef
                        ) || otherRhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherLhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherLhsLinear.y.subtract(
                            otherRhsLinear.y
                        ).add(
                            otherRel.isStrictInequality() ? BigInteger.ONE : BigInteger.ZERO
                        ).compareTo(BigInteger.ZERO) < 0
                    ) {
                        continue;
                    }
                    LLVMHeuristicVariable otherLeft = (LLVMHeuristicVariable)otherLhsLinear.x;
                    Set<LLVMHeuristicVariable> furtherCandidates = new LinkedHashSet<LLVMHeuristicVariable>();
                    furtherCandidates.add(otherLeft);
                    if (newOffsets.x.containsKey(otherLeft)) {
                        for (Pair<LLVMHeuristicVariable, BigInteger> pair : newOffsets.x.get(otherLeft)) {
                            if (pair.y.compareTo(BigInteger.ZERO) >= 0) {
                                furtherCandidates.add(pair.x);
                            }
                        }
                    }
                    for (LLVMHeuristicVariable ref : lhs.getVariables(false)) {
                        if (ref.equals(otherRhsLinear.x)) {
                            for (LLVMHeuristicVariable replacement : furtherCandidates) {
                                LLVMHeuristicRelation inferred = rel.applySubstitution(ref, replacement);
                                if (inferred.getLhs().isSumOfTwoDifferentVariables()) {
                                    newSuitableDirectedInequalities.add(inferred);
                                }
                            }
                        }
                    }
                }
            }
            if (rhs.isSumOfTwoDifferentVariables() && lhs.getVariables(false).size() == 1) {
                newSuitableDirectedInequalities.add(rel);
                for (LLVMHeuristicRelation otherRel : newRels.getDirectedInequalities()) {
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherRhsLinear = otherRel.getRhs().toLinear();
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear = otherRel.getLhs().toLinear();
                    if (
                        !(
                            otherRhsLinear.x instanceof LLVMHeuristicVarRef
                            && otherLhsLinear.x instanceof LLVMHeuristicVarRef
                        ) || otherRhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherLhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherRhsLinear.y.subtract(
                            otherLhsLinear.y
                        ).subtract(
                            otherRel.isStrictInequality() ? BigInteger.ONE : BigInteger.ZERO
                        ).compareTo(BigInteger.ZERO) > 0
                    ) {
                        continue;
                    }
                    LLVMHeuristicVariable otherRight = (LLVMHeuristicVariable)otherRhsLinear.x;
                    Set<LLVMHeuristicVariable> furtherCandidates = new LinkedHashSet<LLVMHeuristicVariable>();
                    furtherCandidates.add(otherRight);
                    if (newOffsets.x.containsKey(otherRight)) {
                        for (Pair<LLVMHeuristicVariable, BigInteger> pair : newOffsets.x.get(otherRight)) {
                            if (pair.y.compareTo(BigInteger.ZERO) <= 0) {
                                furtherCandidates.add(pair.x);
                            }
                        }
                    }
                    for (LLVMHeuristicVariable ref : rhs.getVariables(false)) {
                        if (ref.equals(otherLhsLinear.x)) {
                            for (LLVMHeuristicVariable replacement : furtherCandidates) {
                                LLVMHeuristicRelation inferred = rel.applySubstitution(ref, replacement);
                                if (inferred.getRhs().isSumOfTwoDifferentVariables()) {
                                    newSuitableDirectedInequalities.add(inferred);
                                }
                            }
                        }
                    }
                }
            }
        }
        if (newSuitableDirectedInequalities.isEmpty()) {
            return;
        }
        for (LLVMHeuristicRelation rel : oldRels.getDirectedInequalities()) {
            aborter.checkAbortion();
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs.isSumOfTwoDifferentVariables() && rhs.getVariables(false).size() == 1) {
                oldSuitableDirectedInequalities.add(rel);
                for (LLVMHeuristicRelation otherRel : oldRels.getDirectedInequalities()) {
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherRhsLinear = otherRel.getRhs().toLinear();
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear = otherRel.getLhs().toLinear();
                    if (
                        !(
                            otherRhsLinear.x instanceof LLVMHeuristicVarRef
                            && otherLhsLinear.x instanceof LLVMHeuristicVarRef
                        ) || otherRhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherLhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherLhsLinear.y.subtract(
                            otherRhsLinear.y
                        ).add(
                            otherRel.isStrictInequality() ? BigInteger.ONE : BigInteger.ZERO
                        ).compareTo(BigInteger.ZERO) < 0
                    ) {
                        continue;
                    }
                    LLVMHeuristicVariable otherLeft = (LLVMHeuristicVariable)otherLhsLinear.x;
                    Set<LLVMHeuristicVariable> furtherCandidates = new LinkedHashSet<LLVMHeuristicVariable>();
                    furtherCandidates.add(otherLeft);
                    if (oldOffsets.x.containsKey(otherLeft)) {
                        for (Pair<LLVMHeuristicVariable, BigInteger> pair : oldOffsets.x.get(otherLeft)) {
                            if (pair.y.compareTo(BigInteger.ZERO) >= 0) {
                                furtherCandidates.add(pair.x);
                            }
                        }
                    }
                    for (LLVMHeuristicVariable ref : lhs.getVariables(false)) {
                        if (ref.equals(otherRhsLinear.x)) {
                            for (LLVMHeuristicVariable replacement : furtherCandidates) {
                                LLVMHeuristicRelation inferred = rel.applySubstitution(ref, replacement);
                                if (inferred.getLhs().isSumOfTwoDifferentVariables()) {
                                    oldSuitableDirectedInequalities.add(inferred);
                                }
                            }
                        }
                    }
                }
            }
            if (rhs.isSumOfTwoDifferentVariables() && lhs.getVariables(false).size() == 1) {
                oldSuitableDirectedInequalities.add(rel);
                for (LLVMHeuristicRelation otherRel : oldRels.getDirectedInequalities()) {
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherRhsLinear = otherRel.getRhs().toLinear();
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear = otherRel.getLhs().toLinear();
                    if (
                        !(
                            otherRhsLinear.x instanceof LLVMHeuristicVarRef
                            && otherLhsLinear.x instanceof LLVMHeuristicVarRef
                        ) || otherRhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherLhsLinear.z.compareTo(BigInteger.ONE) != 0
                        || otherRhsLinear.y.subtract(
                            otherLhsLinear.y
                        ).subtract(
                            otherRel.isStrictInequality() ? BigInteger.ONE : BigInteger.ZERO
                        ).compareTo(BigInteger.ZERO) > 0
                    ) {
                        continue;
                    }
                    LLVMHeuristicVariable otherRight = (LLVMHeuristicVariable)otherRhsLinear.x;
                    Set<LLVMHeuristicVariable> furtherCandidates = new LinkedHashSet<LLVMHeuristicVariable>();
                    furtherCandidates.add(otherRight);
                    if (oldOffsets.x.containsKey(otherRight)) {
                        for (Pair<LLVMHeuristicVariable, BigInteger> pair : oldOffsets.x.get(otherRight)) {
                            if (pair.y.compareTo(BigInteger.ZERO) <= 0) {
                                furtherCandidates.add(pair.x);
                            }
                        }
                    }
                    for (LLVMHeuristicVariable ref : rhs.getVariables(false)) {
                        if (ref.equals(otherLhsLinear.x)) {
                            for (LLVMHeuristicVariable replacement : furtherCandidates) {
                                LLVMHeuristicRelation inferred = rel.applySubstitution(ref, replacement);
                                if (inferred.getRhs().isSumOfTwoDifferentVariables()) {
                                    oldSuitableDirectedInequalities.add(inferred);
                                }
                            }
                        }
                    }
                }
            }
        }
        if (oldSuitableDirectedInequalities.isEmpty()) {
            return;
        }
        LLVMHeuristicRelationSet toAdd = new LLVMHeuristicRelationSet();
        for (Map.Entry<BigInteger, Set<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>> newEntry : newOffsets.y.entrySet()) {
            BigInteger offset = newEntry.getKey();
            Set<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>> newSet = newEntry.getValue();
            if (newSet.size() < 2) {
                continue;
            }
            Map<BigInteger, Set<RefPairPair>> matches = new LinkedHashMap<BigInteger, Set<RefPairPair>>();
            for (Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> pair : newSet) {
                for (LLVMSimpleTerm xPartner : newResult.getRefPartners(pair.x, false)) {
                    if (!oldOffsets.x.containsKey(xPartner)) {
                        continue;
                    }
                    aborter.checkAbortion();
                    for (LLVMSimpleTerm yPartner : newResult.getRefPartners(pair.y, false)) {
                        for (Pair<LLVMHeuristicVariable, BigInteger> otherPair : oldOffsets.x.get(xPartner)) {
                            if (!otherPair.x.equals(yPartner) || offset.equals(otherPair.y)) {
                                continue;
                            }
                            // we have pair.x = pair.y + offset and
                            // xPartner = yPartner + otherPair.y and
                            // offset != otherPair.y and
                            // pair.x/xPartner and pair.y/yPartner have been merged
                            if (!matches.containsKey(otherPair.y)) {
                                matches.put(otherPair.y, new LinkedHashSet<RefPairPair>());
                            }
                            matches.get(
                                otherPair.y
                            ).add(
                                new RefPairPair(
                                    pair,
                                    new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(
                                        (LLVMHeuristicVariable)xPartner,
                                        (LLVMHeuristicVariable)yPartner
                                    )
                                )
                            );
                        }
                    }
                }
            }
            for (Set<RefPairPair> match : matches.values()) {
                if (match.size() < 2) {
                    continue;
                }
                // we have at least two changing common distances
                for (RefPairPair firstElement : match) {
                    for (RefPairPair secondElement : match) {
                        if (firstElement == secondElement) {
                            continue;
                        }
                        // check pairwise distinctness
                        if (
                            firstElement.x.x.equals(secondElement.x.x)
                            || firstElement.x.x.equals(secondElement.x.y)
                            || firstElement.x.y.equals(secondElement.x.x)
                            || firstElement.x.y.equals(secondElement.x.y)
                            || firstElement.y.x.equals(secondElement.y.x)
                            || firstElement.y.x.equals(secondElement.y.y)
                            || firstElement.y.y.equals(secondElement.y.x)
                            || firstElement.y.y.equals(secondElement.y.y)
                        ) {
                            continue;
                        }
                        /*
                         * v1_1 = firstElement.x.x
                         * v1_2 = firstElement.x.y
                         * v1_3 = secondElement.x.x
                         * v1_4 = secondElement.x.y
                         * v2_1 = firstElement.y.x
                         * v2_2 = firstElement.y.y
                         * v2_3 = secondElement.y.x
                         * v2_4 = secondElement.y.y
                         */
                        aborter.checkAbortion();
                        // check existence of suitable directed inequality
                        LLVMHeuristicTerm expr114 = termFactory.add(firstElement.x.x, secondElement.x.y);
                        LLVMHeuristicTerm expr214 = termFactory.add(firstElement.y.x, secondElement.y.y);
                        LLVMHeuristicTerm expr123 = termFactory.add(firstElement.x.y, secondElement.x.x);
                        LLVMHeuristicTerm expr223 = termFactory.add(firstElement.y.y, secondElement.y.x);
                        for (LLVMHeuristicRelation newRel : newSuitableDirectedInequalities) {
                            LLVMHeuristicTerm relLeft = newRel.getLhs();
                            LLVMHeuristicTerm relRight = newRel.getRhs();
                            LLVMHeuristicRelationType relType = newRel.getHeuristicRelationType();
                            if (relLeft.equals(expr114)) {
                                for (LLVMHeuristicRelation oldRel : oldSuitableDirectedInequalities) {
                                    if (
                                        oldRel.getHeuristicRelationType() != relType
                                        || !oldRel.getLhs().equals(expr214)
                                    ) {
                                        continue;
                                    }
                                    LLVMHeuristicTerm mergedExpr =
                                        LLVMHeuristicStateFactory.isExprMerged(newResult, relRight, oldRel.getRhs());
                                    if (mergedExpr == null) {
                                        continue;
                                    }
                                    toAdd.add(
                                        relationFactory.createRelation(
                                            relType,
                                            termFactory.add(
                                                newResult.getMergedRef(firstElement.x.y, firstElement.y.y, true),
                                                newResult.getMergedRef(secondElement.x.x, secondElement.y.x, true)
                                            ),
                                            mergedExpr
                                        )
                                    );
                                }
                            } else if (relRight.equals(expr114)) {
                                for (LLVMHeuristicRelation oldRel : oldSuitableDirectedInequalities) {
                                    if (
                                        oldRel.getHeuristicRelationType() != relType
                                        || !oldRel.getRhs().equals(expr214)
                                    ) {
                                        continue;
                                    }
                                    LLVMHeuristicTerm mergedExpr =
                                        LLVMHeuristicStateFactory.isExprMerged(newResult, relLeft, oldRel.getLhs());
                                    if (mergedExpr == null) {
                                        continue;
                                    }
                                    toAdd.add(
                                        relationFactory.createRelation(
                                            relType,
                                            mergedExpr,
                                            termFactory.add(
                                                newResult.getMergedRef(firstElement.x.y, firstElement.y.y, true),
                                                newResult.getMergedRef(secondElement.x.x, secondElement.y.x, true)
                                            )
                                        )
                                    );
                                }
                            } else if (relLeft.equals(expr123)) {
                                for (LLVMHeuristicRelation oldRel : oldSuitableDirectedInequalities) {
                                    if (oldRel.getHeuristicRelationType() != relType || !oldRel.getLhs().equals(expr223)) {
                                        continue;
                                    }
                                    LLVMHeuristicTerm mergedExpr =
                                        LLVMHeuristicStateFactory.isExprMerged(newResult, relRight, oldRel.getRhs());
                                    if (mergedExpr == null) {
                                        continue;
                                    }
                                    toAdd.add(
                                        relationFactory.createRelation(
                                            relType,
                                            termFactory.add(
                                                newResult.getMergedRef(firstElement.x.x, firstElement.y.x, true),
                                                newResult.getMergedRef(secondElement.x.y, secondElement.y.y, true)
                                            ),
                                            mergedExpr
                                        )
                                    );
                                }
                            } else if (relRight.equals(expr123)) {
                                for (LLVMHeuristicRelation oldRel : oldSuitableDirectedInequalities) {
                                    if (
                                        oldRel.getHeuristicRelationType() != relType
                                        || !oldRel.getRhs().equals(expr223)
                                    ) {
                                        continue;
                                    }
                                    LLVMHeuristicTerm mergedExpr =
                                        LLVMHeuristicStateFactory.isExprMerged(newResult, relLeft, oldRel.getLhs());
                                    if (mergedExpr == null) {
                                        continue;
                                    }
                                    toAdd.add(
                                        relationFactory.createRelation(
                                            relType,
                                            mergedExpr,
                                            termFactory.add(
                                                newResult.getMergedRef(firstElement.x.x, firstElement.y.x, true),
                                                newResult.getMergedRef(secondElement.x.y, secondElement.y.y, true)
                                            )
                                        )
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        if (!toAdd.isEmpty()) {
            newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).addRelations(toAdd, aborter).x);
        }
    }
    
    private static boolean isCompatibleStruct(
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct1,
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct2
    ) {
        Set<Pair<BigInteger,LLVMType>> struct1Types = new LinkedHashSet<Pair<BigInteger,LLVMType>>();
        Set<Pair<BigInteger,LLVMType>> struct2Types = new LinkedHashSet<Pair<BigInteger,LLVMType>>();
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : struct1) {
            struct1Types.add(new Pair<BigInteger,LLVMType>(triple.x, triple.y));
        }
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : struct2) {
            struct2Types.add(new Pair<BigInteger,LLVMType>(triple.x, triple.y));
        }
        return struct1Types.containsAll(struct2Types) && struct2Types.containsAll(struct1Types);
    }

    private static Set<LLVMHeuristicVariable> merge_simple_invariants(
        LLVMMemoryRange merged_rng,
        LLVMSimpleMemoryInvariant inst_inv,
        LLVMSimpleMemoryInvariant of_inv,
        LLVMMergeResult newResult,
        boolean instIsNewerState,
        boolean aggressive,
        boolean fastConvergence,
        LLVMParameters params
    ) throws TooExpensiveException {
        LLVMHeuristicVariable mergedVal =
            LLVMHeuristicStateFactory.mergeReferences(
                newResult,
                (LLVMHeuristicVariable)inst_inv.getPointedToValue(),
                (LLVMHeuristicVariable)of_inv.getPointedToValue(),
                merged_rng.getType().getIntegerType(merged_rng.getUnsigned(), params.useBoundedIntegers),
                instIsNewerState,
                aggressive,
                fastConvergence
            );
        newResult.setGeneralizedState(
            newResult.getGeneralizedState().setHeapEntry(merged_rng, new LLVMSimpleMemoryInvariant(mergedVal))
        );
        Set<LLVMHeuristicVariable> res = new HashSet<LLVMHeuristicVariable>(1);
        res.add((LLVMHeuristicVariable)of_inv.getPointedToValue());
        return res;
    }

    private static LLVMMemoryRange merge_heap_range(
        LLVMMemoryRange inst_rng,
        LLVMMemoryRange of_rng,
        LLVMMergeResult newResult,
        boolean instIsNewerState,
        LLVMParameters params,
        boolean aggressive,
        boolean fastConvergence
    ) throws TooExpensiveException {
        LLVMHeuristicVariable mergedLowerBound =
            (LLVMHeuristicVariable)newResult.getMergedRef(inst_rng.getFromRef(), of_rng.getFromRef(), instIsNewerState);
        LLVMHeuristicVariable mergedUpperBound =
            (LLVMHeuristicVariable)newResult.getMergedRef(inst_rng.getToRef(), of_rng.getToRef(), instIsNewerState);
        if (inst_rng instanceof LLVMMemoryRecursiveRange && of_rng instanceof LLVMMemoryRecursiveRange) {
            LLVMHeuristicVariable mergedLength =
                (LLVMHeuristicVariable)newResult.getMergedRef(
                    ((LLVMMemoryRecursiveRange)inst_rng).getLength(),
                    ((LLVMMemoryRecursiveRange)of_rng).getLength(),
                    instIsNewerState
                );
            if (mergedLength == null) {
                mergedLength =
                    LLVMHeuristicStateFactory.mergeReferences(
                        newResult,
                        (LLVMHeuristicVariable)((LLVMMemoryRecursiveRange)inst_rng).getLength(),
                        (LLVMHeuristicVariable)((LLVMMemoryRecursiveRange)of_rng).getLength(),
                        inst_rng.getType().getIntegerType(inst_rng.getUnsigned(), params.useBoundedIntegers),
                        instIsNewerState,
                        aggressive,
                        fastConvergence
                    );
            }
            return new LLVMMemoryRecursiveRange(mergedLowerBound, mergedUpperBound, inst_rng.getType(), mergedLength);
        }
        return new LLVMMemoryRange(mergedLowerBound, mergedUpperBound, of_rng.getType(), of_rng.getUnsigned());
    }

    private static Set<LLVMHeuristicVariable> merge_interval_invariants(
        LLVMMemoryRange merged_rng,
        LLVMIntervalMemoryInvariant inst_inv,
        LLVMIntervalMemoryInvariant of_inv,
        LLVMMergeResult newResult,
        boolean instIsNewerState
    ) {
        if (inst_inv != null && of_inv != null) {
            LLVMMemoryInvariant mergedInvariant =
                inst_inv.join_interval_invariant(newResult.getOfState(instIsNewerState), of_inv).x;
            if (mergedInvariant != null) {
                newResult.setGeneralizedState(
                    newResult.getGeneralizedState().setHeapEntry(merged_rng, mergedInvariant)
                );
            }
        }
        Set<LLVMHeuristicVariable> res = new HashSet<LLVMHeuristicVariable>(1);
        return res;
    }

    private static Set<LLVMHeuristicVariable> merge_invariants(
        LLVMMemoryRange inst_rng,
        LLVMMemoryInvariant inst_inv,
        LLVMMemoryRange of_rng,
        LLVMMemoryInvariant of_inv,
        LLVMMergeResult newResult,
        boolean instIsNewerState,
        LLVMParameters params,
        boolean aggressive,
        boolean fastConvergence
    ) throws TooExpensiveException {
        LLVMMemoryRange merged_range =
            LLVMHeuristicStateFactory.merge_heap_range(inst_rng, of_rng, newResult, instIsNewerState, params, aggressive, fastConvergence);
        if (inst_inv instanceof LLVMSimpleMemoryInvariant && of_inv instanceof LLVMSimpleMemoryInvariant) {
            return
                LLVMHeuristicStateFactory.merge_simple_invariants(
                    merged_range,
                    (LLVMSimpleMemoryInvariant)inst_inv,
                    (LLVMSimpleMemoryInvariant)of_inv,
                    newResult,
                    instIsNewerState,
                    aggressive,
                    fastConvergence,
                    params
                );
        } else if (inst_inv instanceof LLVMSimpleMemoryInvariant && of_inv instanceof LLVMIntervalMemoryInvariant) {
            LLVMIntervalMemoryInvariant inst_int_inv =
                ((LLVMSimpleMemoryInvariant)inst_inv).to_interval_invariant(newResult.getInstState(instIsNewerState));
            return
                LLVMHeuristicStateFactory.merge_interval_invariants(
                    merged_range,
                    inst_int_inv,
                    (LLVMIntervalMemoryInvariant)of_inv,
                    newResult,
                    instIsNewerState
                );
        } else if (inst_inv instanceof LLVMIntervalMemoryInvariant && of_inv instanceof LLVMSimpleMemoryInvariant) {
            // we try to create a weaker version of inst such that it is implied by of - not possible, but the merger
            // will switch inst/of in another call then we can merge the two invariants with the previous case
            return new LinkedHashSet<LLVMHeuristicVariable>();
        } else if (inst_inv instanceof LLVMIntervalMemoryInvariant && of_inv instanceof LLVMIntervalMemoryInvariant) {
            return
                LLVMHeuristicStateFactory.merge_interval_invariants(
                    merged_range,
                    (LLVMIntervalMemoryInvariant)inst_inv,
                    (LLVMIntervalMemoryInvariant)of_inv,
                    newResult,
                    instIsNewerState
                );
        } else {
            throw new IllegalStateException("merging some unknown invariants");
        }
    }

    /**
     * Special case for presence of complex relations: We check whether we also have a complex relation
     * a + up <= low + b with ref = low + c <= up for a (biggest) constant c, (low,up) being an allocated
     * memory area, and we have a reference y such that y = a + d <= b for a (biggest) constant d with c >(=) d. In
     * that case, we additionally try to add the complex relation y + low <(=) ref + a (the strict case only depends on
     * the relation between the constants).
     * @param newResult The merge result under construction.
     * @param rels The relation set to add new knowledge to.
     * @param added The really added relations.
     * @param instState The inst-state.
     * @param instRels The relations in the inst-state.
     * @param ofRelations The relations in the of-state.
     * @param ref A reference.
     * @param instIsNewerState Indicates whether the instance state is the newer state.
     * @return True if at least one complex relation could be inferred. False otherwise.
     */
    private static boolean handleComplexRelationCase(
        LLVMMergeResult newResult,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicRelationSet added,
        LLVMHeuristicState instState,
        ImmutableSet<LLVMHeuristicRelation> instRels,
        LLVMHeuristicRelationSet ofRelations,
        LLVMHeuristicVarRef ref,
        boolean instIsNewerState,
        Abortion aborter
    ) {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        Set<AllocationLimitOffset> allocs =
            LLVMHeuristicStateFactory.findAllocsWithGreaterUpperAndOffset(ofRelations, ofState.getAllocations(), ref);
        if (allocs.isEmpty()) {
            return false;
        }
        final LLVMHeuristicRelationFactory relationFactory = ofState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        boolean res = false;
        for (LLVMHeuristicRelation ofRel : ofRelations) {
            aborter.checkAbortion();
            LLVMHeuristicTerm lhs = ofRel.getLhs();
            LLVMHeuristicTerm rhs = ofRel.getRhs();
            if (!(lhs instanceof LLVMHeuristicOperation && rhs instanceof LLVMHeuristicOperation)) {
                // this is not complex enough
                continue;
            }
            LLVMHeuristicOperation leftOp = (LLVMHeuristicOperation)lhs;
            LLVMHeuristicOperation rightOp = (LLVMHeuristicOperation)rhs;
            if (
                !leftOp.isSimple()
                || !rightOp.isSimple()
                || leftOp.getOperation() != ArithmeticOperationType.ADD
                || rightOp.getOperation() != ArithmeticOperationType.ADD
            ) {
                // this is too complex for us
                continue;
            }
            LLVMHeuristicVariable leftLeft = (LLVMHeuristicVariable)leftOp.getLhs();
            LLVMHeuristicVariable leftRight = (LLVMHeuristicVariable)leftOp.getRhs();
            LLVMHeuristicVariable rightLeft = (LLVMHeuristicVariable)rightOp.getLhs();
            LLVMHeuristicVariable rightRight = (LLVMHeuristicVariable)rightOp.getRhs();
            for (AllocationLimitOffset allocation : allocs) {
                LLVMHeuristicVariable low = (LLVMHeuristicVariable)allocation.x.x;
                LLVMHeuristicVariable up = (LLVMHeuristicVariable)allocation.x.y;
                switch (ofRel.getHeuristicRelationType()) {
                    // TODO also use EQ & LT?
                    //                case LT:
                    //                case EQ:
                    // TODO also check symmetric case for EQ?
                    case LE:
                        LLVMHeuristicVariable a;
                        if (leftLeft.equals(up)) {
                            a = leftRight;
                        } else if (leftRight.equals(up)) {
                            a = leftLeft;
                        } else {
                            a = null;
                        }
                        if (a == null) {
                            continue;
                        }
                        LLVMHeuristicVariable b;
                        if (rightLeft.equals(low)) {
                            b = rightRight;
                        } else if (rightRight.equals(low)) {
                            b = rightLeft;
                        } else {
                            b = null;
                        }
                        if (b == null) {
                            continue;
                        }
                        BigInteger c = allocation.z;
                        // we have a relation a + up <= low + b for an allocation (low,up) with low + c <= up
                        for (
                            LLVMHeuristicVariable y :
                                LLVMHeuristicStateFactory.findBiggestBetweenWithSmallerOffsetThanLimit(
                                    ofState,
                                    ofRelations,
                                    a,
                                    b,
                                    BigInteger.ZERO,
                                    c,
                                    aborter
                                )
                        ) {
                            res |=
                                LLVMHeuristicStateFactory.inferRelation(
                                    newResult,
                                    rels,
                                    added,
                                    instState,
                                    instRels,
                                    relationFactory.lessThanEquals(
                                        termFactory.add(up, y),
                                        termFactory.add(b, allocation.y)
                                    ),
                                    instIsNewerState,
                                    aborter
                                );
                        }
                        break;
                    default:
                        continue;
                }
            }
        }
        return res;
    }

    /**
     * This method is used to detect indices for arrays and learn corresponding relations.
     * If we merge two different constant references cNew and cOld to cMerged and the relations
     * yNew = cNew * c + xNew
     * yOld = cOld * c + xOld
     * hold for non-constant references xNew, xOld, yNew, yOld and a constant c such that xNew is merged with xOld to
     * xMerged, yNew is merged with yOld to yMerged, and yNew and yOld are associated references, then infer the
     * relation
     * yMerged = cMerged * c + xMerged.
     * @param newResult The merge result under construction.
     * @param newOffsets The offset maps for the newer state. Entries c -> {(x, y),...} in the CommonOffsetMap
     *                   represent the knowledge x = y + c. Entries x -> {(y, c),...} in the OffsetMap also represent
     *                   the knowledge x = y + c.
     * @param oldOffsets The offset maps for the older state.
     */
    private static void handleConstantArrayIndices(
        LLVMMergeResult newResult,
        Pair<LLVMOffsetMap, LLVMCommonOffsetMap> newOffsets,
        Pair<LLVMOffsetMap, LLVMCommonOffsetMap> oldOffsets,
        Abortion aborter
    ) {
        LLVMHeuristicState newState = (LLVMHeuristicState)newResult.getNewerState();
        LLVMHeuristicState oldState = (LLVMHeuristicState)newResult.getOlderState();
        LLVMHeuristicState mergedState = (LLVMHeuristicState)newResult.getGeneralizedState();
        final LLVMHeuristicRelationFactory relationFactory = mergedState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        /*
         * Find candidates for constant c. To guess the constant c, consider the types of program variables. Only those
         * types where we have a pointer to are relevant.
         */
        Set<BigInteger> cs = new LinkedHashSet<BigInteger>();
        for (ImmutablePair<LLVMSymbolicVariable, LLVMType> val : mergedState.getProgramVariables().values()) {
            if (val.y.isPointerType()) {
                Queue<LLVMType> types = new ArrayDeque<LLVMType>();
                types.offer(val.y.getThisAsPointerType().getTargetType());
                while (!types.isEmpty()) {
                    LLVMType type = types.poll();
                    cs.add(BigInteger.valueOf(IntegerUtils.bitsToBytes(type.size())));
                    if (type.isAggregateType()) {
                        types.addAll(type.getSubtypes());
                    }
                }
            }
        }
        // find merged pairs of constants cNew and cOld
        Map<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> refMapping = newResult.getRefMapping();
        for (Pair<LLVMSimpleTerm, LLVMSimpleTerm> merged : refMapping.keySet()) {
            if (!((LLVMHeuristicVariable)merged.x).isConcrete() || !((LLVMHeuristicVariable)merged.y).isConcrete()) {
                continue;
            }
            aborter.checkAbortion();
            BigInteger cNew = ((LLVMHeuristicConstRef)merged.x).getIntegerValue();
            BigInteger cOld = ((LLVMHeuristicConstRef)merged.y).getIntegerValue();
            LLVMHeuristicVariable cMerged = (LLVMHeuristicVariable)newResult.getMergedRef(merged.x, merged.y, true);
            ImmutableMap<LLVMHeuristicVariable, Integer> oldAssocs = oldState.getAssociations();
            // check associated references in newer state
            for (LLVMHeuristicVariable yNew : newState.getAssociations().keySet()) {
                // check references with constant distance to yNew
                Set<Pair<LLVMHeuristicVariable, BigInteger>> newOffsetSet = newOffsets.x.get(yNew);
                if (newOffsetSet == null) {
                    continue;
                }
                for (Pair<LLVMHeuristicVariable, BigInteger> xNewCandidate : newOffsetSet) {
                    BigInteger c = null;
                    aborter.checkAbortion();
                    if (cNew.compareTo(BigInteger.ZERO) == 0) {
                        if (xNewCandidate.y.compareTo(BigInteger.ZERO) != 0) {
                            continue;
                        }
                        if (cOld.compareTo(BigInteger.ZERO) == 0) {
                            continue;
                        }
                    } else {
                        BigInteger[] divRes = xNewCandidate.y.divideAndRemainder(cNew);
                        if (divRes[1].compareTo(BigInteger.ZERO) != 0) {
                            // if the constant distance is not divisible by the merged constant, dismiss this candidate
                            continue;
                        }
                        c = divRes[0];
                        if (!cs.contains(c)) {
                            // if the constant c is not relevant according to the program types, dismiss this candidate
                            continue;
                        }
                    }
                    LLVMHeuristicVariable xNew = xNewCandidate.x;
                    for (LLVMSimpleTerm yOld : newResult.getRefPartners(yNew, false)) {
                        if (!oldAssocs.containsKey(yOld)) {
                            // if the merge partner is not associated, dismiss this merge partner
                            continue;
                        }
                        Set<Pair<LLVMHeuristicVariable, BigInteger>> oldOffsetSet = oldOffsets.x.get(yOld);
                        if (oldOffsetSet == null) {
                            continue;
                        }
                        for (Pair<LLVMHeuristicVariable, BigInteger> xOldCandidate : oldOffsetSet) {
                            final BigInteger cFinal;
                            aborter.checkAbortion();
                            if (cOld.compareTo(BigInteger.ZERO) == 0) {
                                if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                                    assert (c != null) : "Trying to merge two constant zeros. Why?";
                                }
                                if (xOldCandidate.y.compareTo(BigInteger.ZERO) != 0) {
                                    continue;
                                }
                                cFinal = c;
                            } else {
                                BigInteger[] divResOld = xOldCandidate.y.divideAndRemainder(cOld);
                                if (
                                    divResOld[1].compareTo(BigInteger.ZERO) != 0
                                    || (c != null && c.compareTo(divResOld[0]) != 0)
                                ) {
                                    // if the constant distance is not divisible by the merged constant or the division
                                    // result is not the same as for the newer state, dismiss this candidate
                                    continue;
                                }
                                cFinal = divResOld[0];
                            }
                            LLVMHeuristicVariable xOld = xOldCandidate.x;
                            LLVMHeuristicVariable xMerged =
                                (LLVMHeuristicVariable)newResult.getMergedRef(xNew, xOld, true);
                            if (xMerged == null) {
                                continue;
                            }
                            LLVMHeuristicVariable yMerged =
                                (LLVMHeuristicVariable)newResult.getMergedRef(yNew, yOld, true);
                            // add relation yMerged = c * cMerged + xMerged
                            mergedState =
                                mergedState.addRelation(
                                    relationFactory.equalTo(
                                        yMerged,
                                        termFactory.add(
                                            termFactory.mult(termFactory.constant(cFinal), cMerged),
                                            xMerged
                                        )
                                    ),
                                    aborter
                                );
                        }
                    }
                }
            }
        }
        newResult.setGeneralizedState(mergedState);
    }

    /**
     * Add those merged references to the set of initial heap addresses where both source references have been such a
     * reference.
     * @param newResult The generalization result under construction.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @throws TooExpensiveException If this is too expensive.
     */
    private static void handleInitialHeapAddresses(LLVMMergeResult newResult, boolean aggressive, boolean fastConvergence) throws TooExpensiveException {
        Map<Integer, LLVMHeuristicVariable> genInitHeapAddrs = new LinkedHashMap<Integer, LLVMHeuristicVariable>();
        final LLVMHeuristicState oldState = (LLVMHeuristicState)newResult.getOlderState();
        ImmutableMap<Integer, LLVMHeuristicVariable> oldInitHeapAddrs = oldState.getInitialHeapAddresses();
        ImmutableMap<Integer, LLVMHeuristicVariable> newInitHeapAddrs =
            ((LLVMHeuristicState)newResult.getNewerState()).getInitialHeapAddresses();
        Set<Integer> common = new LinkedHashSet<Integer>(oldInitHeapAddrs.keySet());
        common.retainAll(newInitHeapAddrs.keySet());
        IntegerType pointerType =
            oldState.getModule().getPointerType(oldState.getStrategyParamters().useBoundedIntegers);
        for (Integer i : common) {
            genInitHeapAddrs.put(
                i,
                LLVMHeuristicStateFactory.mergeReferences(
                    newResult,
                    newInitHeapAddrs.get(i),
                    oldInitHeapAddrs.get(i),
                    pointerType,
                    true,
                    aggressive,
                    fastConvergence
                )
            );
        }
        newResult.setGeneralizedState(
            ((LLVMHeuristicState)newResult.getGeneralizedState()).setInitialHeapAddresses(genInitHeapAddrs)
        );
    }

    /**
     * Tries to find corresponding heap entries and merges the respective references which have not yet been merged
     * (only cares about non pointwise heap invariants).
     * @param newResult The generalization result currently constructed.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     *          in order to speed up graph construction?
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @throws TooExpensiveException If this got too expensive.
     */
    private static void handleNonPointwiseHeapInvariants(LLVMMergeResult newResult, boolean instIsNewerState, boolean aggressive, boolean fastConvergence)
    throws TooExpensiveException {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        final LLVMParameters params = instState.getStrategyParamters();
        ImmutableMap<LLVMMemoryRange,LLVMMemoryInvariant> ofHeap = ofState.getMemory();
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> instHeap = instState.getMemory();
        // added contains all references which have already been merged (at least once)
        Set<LLVMSimpleTerm> added = new LinkedHashSet<LLVMSimpleTerm>(newResult.getMergedOfRefs(instIsNewerState));
        Queue<LLVMSimpleTerm> todo = new ArrayDeque<LLVMSimpleTerm>(added);
        while (!todo.isEmpty()) {
            LLVMSimpleTerm ofRef = todo.poll();
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> ofPointsToInf : ofHeap.entrySet()) {
                LLVMMemoryRange ofRange = ofPointsToInf.getKey();
                if (ofRange.isPointwise()) {
                    continue;
                }
                LLVMSimpleTerm ofLowerBound = null;
                LLVMSimpleTerm ofUpperBound = null;
                if (ofRange.getFromRef().equals(ofRef)) {
                    ofLowerBound = ofRef;
                    ofUpperBound = ofRange.getToRef();
                } else if (ofRange.getToRef().equals(ofRef)) {
                    ofLowerBound = ofRange.getFromRef();
                    ofUpperBound = ofRef;
                } else {
                    continue;
                }
                boolean foundPartnerRange = false;
                for (LLVMSimpleTerm instLowerBound : newResult.getRefPartners(ofLowerBound, instIsNewerState)) {
                    for (LLVMSimpleTerm instUpperBound : newResult.getRefPartners(ofUpperBound, instIsNewerState)) {
                        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> instPointsToInf : instHeap.entrySet()) {
                            LLVMMemoryRange instRange = instPointsToInf.getKey();
                            if (
                                !instRange.getFromRef().equals(instLowerBound)
                                || !instRange.getToRef().equals(instUpperBound)
                                || !ofRange.getType().equals(instRange.getType())
                            ) {
                                continue;
                            }
                            foundPartnerRange = true;
                            Set<LLVMHeuristicVariable> vals_to_continue =
                                LLVMHeuristicStateFactory.merge_invariants(
                                    instRange,
                                    instPointsToInf.getValue(),
                                    ofRange,
                                    ofPointsToInf.getValue(),
                                    newResult,
                                    instIsNewerState,
                                    params,
                                    aggressive,
                                    fastConvergence
                                );
                            for (LLVMHeuristicVariable ref : vals_to_continue) {
                                // test is needed to avoid non-termination on cyclic heap information
                                if (!added.contains(ref)) {
                                    added.add(ref);
                                    todo.add(ref);
                                }
                            }
                        }
                    }
                }
//                for (LLVMSimpleTerm instLowerBound : newResult.getRefPartners(ofLowerBound, instIsNewerState)) {
//                    if (instLowerBound instanceof LLVMHeuristicVariable && ofUpperBound instanceof LLVMHeuristicVariable &&
//                        !(ofLowerBound.equals(ofUpperBound)) && newResult.getRefPartners(ofUpperBound, instIsNewerState).isEmpty()) {
//                        LLVMSymbolicVariable newRef;
//                        try {
//                            newRef =
//                                mergeReferences(
//                                    newResult,
//                                    (LLVMHeuristicVariable)instLowerBound,
//                                    (LLVMHeuristicVariable)ofUpperBound,
//                                    IntegerType.UI64,
//                                    instIsNewerState
//                                );
//                        } catch (TooExpensiveException e) {
//                            continue;
//                        }
//                        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> instPointsToInf : instHeap.entrySet()) {
//                            LLVMMemoryRange instRange = instPointsToInf.getKey();
//                            if (
//                                !instRange.getFromRef().equals(instLowerBound)
//                                || !instRange.getToRef().equals(instLowerBound)
//                                || !ofRange.getType().equals(instRange.getType())
//                            ) {
//                                continue;
//                            }
//                            foundPartnerRange = true;
//                            Set<LLVMHeuristicVariable> vals_to_continue =
//                                LLVMHeuristicStateFactory.merge_invariants(
//                                    instRange,
//                                    instPointsToInf.getValue(),
//                                    ofRange,
//                                    ofPointsToInf.getValue(),
//                                    newResult,
//                                    instIsNewerState,
//                                    params
//                                );
//                            for (LLVMHeuristicVariable ref : vals_to_continue) {
//                                // test is needed to avoid non-termination on cyclic heap information
//                                if (!added.contains(ref)) {
//                                    added.add(ref);
//                                    todo.add(ref);
//                                }
//                            }
//                        }
//                    }
//                }
                //if (!foundPartnerRange && ofPointsToInf.getValue() instanceof LLVMIntervalMemoryInvariant) {
                //    throw new TooExpensiveException("No corresponding interval invariant found!");
                //}
            }
        }
    }

    /**
     * Checks the given non-simple equation to match an off-by-constant pattern (i.e., c + x = d + y) and in that case
     * tries to infer weak relations instead of the equation or (if that fails) tries to infer weak relations for x
     * from strict ones for y and one strict relation between x and y. Moreover, we check whether we also have a
     * complex relation a + up <= low + b with x being less than up, (low,up) being an allocated memory area, and we
     * have a reference y such that a + d = y <= b for a (biggest) constant d. In that case, we additionally try to add
     * the complex relation x + a < y + low. The inferred relations are added to the relation set rels.
     * @param newResult The generalization result under construction.
     * @param rels The new relations.
     * @param added The set of really added relations.
     * @param instState The inst-state.
     * @param ofRelations The relations in the of-state.
     * @param ofRel The non-simple equation from the of-state to check for an off-by-constant pattern.
     * @param instIsNewerState Flag indicating whether the inst-state is the newer state.
     */
    private static void handleOffByConstantPattern(
        LLVMMergeResult newResult,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicRelationSet added,
        LLVMHeuristicState instState,
        LLVMHeuristicRelationSet ofRelations,
        LLVMHeuristicRelation ofRel,
        boolean instIsNewerState,
        Abortion aborter
    ) {
        final LLVMHeuristicRelationFactory relationFactory = instState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        ImmutableSet<LLVMHeuristicRelation> instRelations = instState.getRelations();
        LLVMHeuristicTerm lhs = ofRel.getLhs();
        LLVMHeuristicTerm rhs = ofRel.getRhs();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = lhs.toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rhs.toLinear();
        if (
            !(
                lhsLinear.x instanceof LLVMHeuristicVarRef
                && rhsLinear.x instanceof LLVMHeuristicVarRef
                && lhsLinear.z.compareTo(BigInteger.ONE) == 0
                && rhsLinear.z.compareTo(BigInteger.ONE) == 0
            )
        ) {
            // no off-by-constant pattern
            return;
        }
        final LLVMHeuristicVarRef bigger;
        final LLVMHeuristicVarRef smaller;
        final BigInteger offset;
        if (lhsLinear.y.compareTo(rhsLinear.y) < 0) {
            bigger = (LLVMHeuristicVarRef)lhsLinear.x;
            smaller = (LLVMHeuristicVarRef)rhsLinear.x;
            offset = rhsLinear.y.subtract(lhsLinear.y);
        } else {
            bigger = (LLVMHeuristicVarRef)rhsLinear.x;
            smaller = (LLVMHeuristicVarRef)lhsLinear.x;
            offset = lhsLinear.y.subtract(rhsLinear.y);
        }
        LLVMHeuristicTerm sum = termFactory.add(smaller, termFactory.constant(offset));
        /*
         *  We have a relation of the form smaller + offset = bigger with offset > 0 in the of-state, but we do not
         *  have ren(smaller) + offset = ren(bigger) in the inst-state. First try to infer
         *  ren(smaller) + offset <= ren(bigger) or ren(smaller) + offset >= ren(bigger) in the inst-state.
         */
        if (
            !LLVMHeuristicStateFactory.inferRelation(
                newResult,
                rels,
                added,
                instState,
                instRelations,
                relationFactory.lessThanEquals(sum, bigger),
                instIsNewerState,
                aborter
            )
        ) {
            // we do not have ren(smaller) + offset <= ren(bigger)
            // try to infer ren(bigger) <= ren(smaller) + offset and ren(smaller) < ren(bigger)
            LLVMHeuristicStateFactory.inferRelation(
                newResult,
                rels,
                added,
                instState,
                instRelations,
                relationFactory.lessThanEquals(bigger, sum),
                instIsNewerState,
                aborter
            );
            if (
                !LLVMHeuristicStateFactory.inferRelation(
                    newResult,
                    rels,
                    added,
                    instState,
                    instRelations,
                    relationFactory.lessThan(smaller, bigger),
                    instIsNewerState,
                    aborter
                )
            ) {
                // Finally, try to infer at least the weak directed inequality.
                LLVMHeuristicStateFactory.inferRelation(
                    newResult,
                    rels,
                    added,
                    instState,
                    instRelations,
                    relationFactory.lessThanEquals(smaller, bigger),
                    instIsNewerState,
                    aborter
                );
            }
        }
        if (offset.compareTo(BigInteger.ONE) == 0) {
            // special case for offset = 1: try to find relations of the form smaller < expr or expr < bigger in the
            // of-state and infer weak relations ren(bigger) <= ren(expr) or ren(expr) <= ren(smaller)
            LLVMHeuristicStateFactory.handleOffByOnePattern(
                newResult,
                instState,
                ofRelations,
                instRelations,
                rels,
                added,
                smaller,
                bigger,
                instIsNewerState,
                aborter
            );
        }
        /*
         * Special case for presence of complex relations: We check whether we also have a complex relation
         * a + up <= low + b with bigger/smaller plus some offset being less than up, (low,up) being an allocated
         * memory area, and we have a reference y such that a + d = y <= b for a (biggest) constant d. In that case, we
         * additionally try to add the complex relation simpleNode + a < y + low.
         */
        if (
            !LLVMHeuristicStateFactory.handleComplexRelationCase(
                newResult,
                rels,
                added,
                instState,
                instRelations,
                ofRelations,
                bigger,
                instIsNewerState,
                aborter
            )
        ) {
            LLVMHeuristicStateFactory.handleComplexRelationCase(
                newResult,
                rels,
                added,
                instState,
                instRelations,
                ofRelations,
                smaller,
                instIsNewerState,
                aborter
            );
        }
    }

    /**
     * Special case for offset = 1: Try to find relations of the form smaller < expr or expr < bigger in the of-state
     * and try to infer weak relations ren(bigger) <= ren(expr) or ren(expr) <= ren(smaller).
     * @param newResult The merge result under construction.
     * @param instState The inst-state.
     * @param ofRelations The relations in the of-state.
     * @param instRelations The relations in the inst-state.
     * @param rels The relation set to add new knowledge to.
     * @param added The really added relations.
     * @param smaller The smaller reference.
     * @param bigger The bigger reference.
     * @param instIsNewerState Is the inst-state the newer state?
     */
    private static void handleOffByOnePattern(
        LLVMMergeResult newResult,
        LLVMHeuristicState instState,
        LLVMHeuristicRelationSet ofRelations,
        ImmutableSet<LLVMHeuristicRelation> instRelations,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicRelationSet added,
        LLVMHeuristicVariable smaller,
        LLVMHeuristicVariable bigger,
        boolean instIsNewerState,
        Abortion aborter
    ) {
        final LLVMHeuristicRelationFactory relationFactory = instState.getRelationFactory();
        for (LLVMHeuristicRelation otherOfRel : ofRelations) {
            if (!otherOfRel.isDirectedInequality()) {
                continue;
            }
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = otherOfRel.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = otherOfRel.getRhs().toLinear();
            BigInteger offset = lhsLinear.y.subtract(rhsLinear.y);
            if (!otherOfRel.isStrictInequality()) {
                offset = offset.subtract(BigInteger.ONE);
            }
            if (
                lhsLinear.x == null
                || rhsLinear.x == null
                || lhsLinear.z.compareTo(BigInteger.ONE) != 0
                || rhsLinear.z.compareTo(BigInteger.ONE) != 0
                || offset.compareTo(BigInteger.ZERO) != 0
            ) {
                continue;
            }
            if (lhsLinear.x.equals(smaller)) {
                // we found a relation of the form smaller < rhsLinear.x in the of-state
                // now try to infer ren(bigger) <= ren(rhsLinear.x) in inst-state
                LLVMHeuristicStateFactory.inferRelation(
                    newResult,
                    rels,
                    added,
                    instState,
                    instRelations,
                    relationFactory.lessThanEquals(bigger, rhsLinear.x),
                    instIsNewerState,
                    aborter
                );
            } else if (rhsLinear.x.equals(bigger)) {
                // we found a relation of the form lhsLinear.x < bigger in the of-state
                // now try to infer ren(lhsLinear.x) <= ren(smaller) in inst-state
                LLVMHeuristicStateFactory.inferRelation(
                    newResult,
                    rels,
                    added,
                    instState,
                    instRelations,
                    relationFactory.lessThanEquals(lhsLinear.x, smaller),
                    instIsNewerState,
                    aborter
                );
            }
        }
    }

    /**
     * Tries to find corresponding heap entries and merges the respective references which have not yet been merged (only cares about pointwise heap information).
     * @param newResult The generalization result currently constructed.
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @throws TooExpensiveException If this got too expensive.
     */
    private static void handlePointwiseHeap(LLVMMergeResult newResult, boolean instIsNewerState, boolean aggressive, boolean fastConvergence, Abortion aborter)
    throws TooExpensiveException {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        final boolean useBoundedIntegers = ofState.getStrategyParamters().useBoundedIntegers;
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> ofHeap = ofState.getMemory();
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> instHeap = instState.getMemory();
        // added contains all references which have already been merged (at least once)
        Set<LLVMSimpleTerm> added = new LinkedHashSet<LLVMSimpleTerm>(newResult.getMergedOfRefs(instIsNewerState));
        Queue<LLVMSimpleTerm> todo = new ArrayDeque<LLVMSimpleTerm>(added);
        while (!todo.isEmpty()) {
            LLVMHeuristicVariable ofRef = (LLVMHeuristicVariable)todo.poll();
            outerFor: for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> ofEntry : ofHeap.entrySet()) {
                LLVMMemoryRange ofKey = ofEntry.getKey();
                LLVMMemoryInvariant ofValue = ofEntry.getValue();
                if (! ofKey.isPointwise() || !ofKey.getFromRef().equals(ofRef)) {
                    continue;
                }
                for (LLVMSimpleTerm instRef : newResult.getRefPartners(ofRef, instIsNewerState)) {
                    if (aggressive && ofValue instanceof LLVMCombinedMemoryInvariant && instRef instanceof LLVMConstant
                            && ((LLVMCombinedMemoryInvariant)ofValue).getLastRecursivePointer().equals(instRef)) {
                        LLVMMemoryRecursiveRange ofRange = (LLVMMemoryRecursiveRange) ofKey;
                        LLVMSimpleTerm mergedRef = newResult.getMergedRef(instRef, ofRef, instIsNewerState);
                        if (mergedRef == null) {
                            continue;
                        }
                        LLVMValue mergedLength =
                            mergeValues(
                                newResult,
                                LiteralInt.create(((LLVMConstant)instRef).getIntegerValue()),
                                ofState.getValue((LLVMHeuristicVariable)ofRange.getLength()),
                                IntegerType.UI32,
                                instIsNewerState,
                                fastConvergence
                            );
                        LLVMHeuristicTermFactory termFactory = ((LLVMHeuristicState)newResult.getGeneralizedState()).getRelationFactory().getTermFactory();
                        LLVMHeuristicVariable mergedLengthRef = termFactory.freshVariable();
                        newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue(mergedLengthRef, mergedLength));
                        LLVMMemoryRecursiveRange mergedRange = new LLVMMemoryRecursiveRange(mergedRef, mergedRef, ofRange.getType(), mergedLengthRef);
                        LLVMCombinedMemoryInvariant mergedInvariant;
                        Map<BigInteger,LLVMMemoryInvariant> ofInvs = ((LLVMCombinedMemoryInvariant)ofValue).getInvariants();
                        Map<BigInteger,LLVMMemoryInvariant> genInvs = new LinkedHashMap<>();
                        for (Map.Entry<BigInteger,LLVMMemoryInvariant> ofInvPair : ofInvs.entrySet()) {
                            LLVMMemoryInvariant ofInv = ofInvPair.getValue();
                            if (ofInv instanceof LLVMComplexMemoryInvariant) {
                                LLVMType ofType = ((LLVMComplexMemoryInvariant)ofInv).getType();
                                LLVMHeuristicVariable mergedFirstRef = termFactory.freshVariable();
                                LLVMValue mergedFirstVal = ofType.getInitializedIntValue(false, useBoundedIntegers);
                                newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue(mergedFirstRef, mergedFirstVal));
                                LLVMHeuristicVariable mergedLastRef;
                                if (ofType.isPointerType() && ofType.getThisAsPointerType().pointsToStruct()) {
                                    mergedLastRef = new LLVMHeuristicConstRef(((LLVMConstant)instRef).getIntegerValue());
                                } else {
                                    mergedLastRef = termFactory.freshVariable();
                                    LLVMValue mergedLastVal = ofType.getInitializedIntValue(false, useBoundedIntegers);
                                    newResult.setGeneralizedState(((LLVMHeuristicState)newResult.getGeneralizedState()).setValue(mergedLastRef, mergedLastVal));
                                }
                                LLVMAdditiveChange mergedChange = ((LLVMComplexMemoryInvariant)ofInv).getChange();
                                genInvs.put(ofInvPair.getKey(), new LLVMComplexMemoryInvariant(mergedFirstRef,mergedLastRef,mergedChange,ofType));
                            }
                        }
                        mergedInvariant = new LLVMCombinedMemoryInvariant(genInvs);
                        newResult.setGeneralizedState(
                            newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
                        );
                        // do not use the same list invariant twice
                        continue outerFor;
                    }
                    for ( Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> instEntry : instHeap.entrySet() ) {
                        LLVMMemoryRange instKey = instEntry.getKey();
                        LLVMMemoryInvariant instValue = instEntry.getValue();
                        if (!instKey.getFromRef().equals(instRef) || !instKey.isPointwise() || !ofKey.getType().equals(instKey.getType())) {
                            continue;
                        }
                        IntegerType type = instKey.getType().getIntegerType(instKey.getUnsigned(), useBoundedIntegers);
                        // we need to use local variables here as the merge operations change newResult
                        if (ofValue instanceof LLVMSimpleMemoryInvariant && instValue instanceof LLVMSimpleMemoryInvariant) {
                            LLVMHeuristicVariable ofVal =
                                (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)ofValue).getPointedToValue();
                            LLVMHeuristicVariable mergedVal =
                                LLVMHeuristicStateFactory.mergeReferences(
                                    newResult,
                                    (LLVMHeuristicVariable)
                                        ((LLVMSimpleMemoryInvariant)instValue).getPointedToValue(),
                                    ofVal,
                                    type,
                                    instIsNewerState,
                                    aggressive,
                                    fastConvergence
                                );
                            LLVMHeuristicVariable mergedRef =
                                (LLVMHeuristicVariable)newResult.getMergedRef(instRef, ofRef, instIsNewerState);
                            newResult.setGeneralizedState(
                                newResult.getGeneralizedState().setHeapEntry(
                                    new LLVMMemoryRange(mergedRef, mergedRef, ofKey.getType(), ofKey.getUnsigned()),
                                    new LLVMSimpleMemoryInvariant(mergedVal)
                                )
                            );
                            // test is needed to avoid non-termination on cyclic heap information
                            if (!added.contains(ofVal)) {
                                added.add(ofVal);
                                todo.offer(ofVal);
                            }
                        } else {
                            LLVMMemoryRange mergedRange =
                                LLVMHeuristicStateFactory.merge_heap_range(
                                    instKey,
                                    ofEntry.getKey(),
                                    newResult,
                                    instIsNewerState,
                                    instState.getStrategyParamters(),
                                    aggressive,
                                    fastConvergence
                                );
                            if (instValue instanceof LLVMIntervalMemoryInvariant && ofValue instanceof LLVMIntervalMemoryInvariant) {
                                LLVMMemoryInvariant mergedInvariant =
                                    ((LLVMIntervalMemoryInvariant)instValue).join_interval_invariant(
                                        newResult.getOfState(instIsNewerState),
                                        (LLVMIntervalMemoryInvariant)ofValue
                                    ).x;
                                if (mergedInvariant != null) {
                                    newResult.setGeneralizedState(
                                        newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
                                    );
                                }
                            } else if (instValue instanceof LLVMSimpleMemoryInvariant && ofValue instanceof LLVMIntervalMemoryInvariant) {
                                LLVMIntervalMemoryInvariant instInterval =
                                    ((LLVMSimpleMemoryInvariant)instValue).to_interval_invariant(newResult.getInstState(instIsNewerState));
                                LLVMMemoryInvariant mergedInvariant =
                                    instInterval.join_interval_invariant(
                                        newResult.getOfState(instIsNewerState),
                                        (LLVMIntervalMemoryInvariant)ofValue
                                    ).x;
                                if (mergedInvariant != null) {
                                    newResult.setGeneralizedState(
                                        newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
                                    );
                                } 
                            } else if (instValue instanceof LLVMIntervalMemoryInvariant && ofValue instanceof LLVMSimpleMemoryInvariant) {
                                LLVMIntervalMemoryInvariant ofInterval =
                                    ((LLVMSimpleMemoryInvariant)ofValue).to_interval_invariant(newResult.getOfState(instIsNewerState));
                                LLVMMemoryInvariant mergedInvariant =
                                    ((LLVMIntervalMemoryInvariant)instValue).join_interval_invariant(
                                        newResult.getOfState(instIsNewerState),
                                        ofInterval
                                    ).x;
                                if (mergedInvariant != null) {
                                    newResult.setGeneralizedState(
                                        newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
                                    );
                                } 
                            } else if (instValue instanceof LLVMCombinedMemoryInvariant && ofValue instanceof LLVMCombinedMemoryInvariant) {
                                LLVMCombinedMemoryInvariant mergedInvariant;
                                Map<BigInteger,LLVMMemoryInvariant> ofInvs = ((LLVMCombinedMemoryInvariant)ofValue).getInvariants();
                                Map<BigInteger,LLVMMemoryInvariant> instInvs = ((LLVMCombinedMemoryInvariant)instValue).getInvariants();
                                Map<BigInteger,LLVMMemoryInvariant> genInvs = new LinkedHashMap<>();
                                LLVMHeuristicVariable mergedFirstVal = null;
                                LLVMHeuristicVariable mergedLastVal = null;
                                for (Map.Entry<BigInteger,LLVMMemoryInvariant> ofInvPair : ofInvs.entrySet()) {
                                    LLVMMemoryInvariant ofInv = ofInvPair.getValue();
                                    LLVMMemoryInvariant instInv = instInvs.get(ofInvPair.getKey());
                                    if (ofInv instanceof LLVMComplexMemoryInvariant && instInv instanceof LLVMComplexMemoryInvariant) {
                                        LLVMType ofType = ((LLVMComplexMemoryInvariant)ofInv).getType();
                                        LLVMSimpleTerm ofFirst = ((LLVMComplexMemoryInvariant)ofInv).getFirstValue();
                                        LLVMSimpleTerm instFirst = ((LLVMComplexMemoryInvariant)instInv).getFirstValue();
                                        if (ofFirst instanceof LLVMHeuristicVariable && instFirst instanceof LLVMHeuristicVariable) {
                                            mergedFirstVal =
                                                LLVMHeuristicStateFactory.mergeReferences(
                                                    newResult,
                                                    (LLVMHeuristicVariable)instFirst,
                                                    (LLVMHeuristicVariable)ofFirst,
                                                    ofType.getIntegerType(false, useBoundedIntegers),
                                                    instIsNewerState,
                                                    aggressive,
                                                    fastConvergence
                                                );
                                        }
                                        LLVMSimpleTerm ofLast = ((LLVMComplexMemoryInvariant)ofInv).getLastValue();
                                        LLVMSimpleTerm instLast = ((LLVMComplexMemoryInvariant)instInv).getLastValue();
                                        if (ofLast instanceof LLVMHeuristicVariable && instLast instanceof LLVMHeuristicVariable) {
                                            mergedLastVal =
                                                LLVMHeuristicStateFactory.mergeReferences(
                                                    newResult,
                                                    (LLVMHeuristicVariable)instLast,
                                                    (LLVMHeuristicVariable)ofLast,
                                                    ofType.getIntegerType(false, useBoundedIntegers),
                                                    instIsNewerState,
                                                    aggressive,
                                                    fastConvergence
                                                );
                                        }
                                        LLVMAdditiveChange mergedChange = null;
                                        LLVMAdditiveChange ofChange = ((LLVMComplexMemoryInvariant)ofInv).getChange();
                                        LLVMAdditiveChange instChange = ((LLVMComplexMemoryInvariant)instInv).getChange();
                                        if (ofChange.getLinearRate() != null && instChange.getLinearRate() != null &&
                                            ((LLVMComplexMemoryInvariant)ofInv).getChange().getLinearRate().equals(((LLVMComplexMemoryInvariant)instInv).getChange().getLinearRate())) {
                                            mergedChange = new LLVMAdditiveChange(((LLVMComplexMemoryInvariant)ofInv).getChange().getLinearRate());
                                        } else {
                                            mergedChange = new LLVMAdditiveChange(null, LLVMSortedType.min(ofChange.getSortedType(), instChange.getSortedType()));
                                        }
                                        genInvs.put(ofInvPair.getKey(), new LLVMComplexMemoryInvariant(mergedFirstVal,mergedLastVal,mergedChange,ofType));
                                    }
                                }
                                mergedInvariant = new LLVMCombinedMemoryInvariant(genInvs);
                                newResult.setGeneralizedState(
                                    newResult.getGeneralizedState().setHeapEntry(mergedRange, mergedInvariant)
                                );
                                // do not use the same list invariant twice
                                continue outerFor;
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * Adds all relations from the progenitor state which also hold in the instance state (where
     * <code>instIsNewerState</code> indicates whether the instance state is the newer or the older one) to the result.
     * Variables, allocated memory areas, and heap information must already have been handled before calling this
     * method.
     * The problem here are states which look like the following:
     *  %x: v1, %y: v1        v1 < 10
     *  %x: v2, %y: v3        v2 < 10
     * The merge result here should be:
     *  %x: v4, %y: v5        v4 < 10
     * However, we need to consider all possible renamings when checking if the respective relation holds in the other
     * state. So what we do is:
     *  (1) Iterate over all relations
     *  (2) Iterate over all variables in each relation
     *  (3) Iterate over all partners of these, producing a substitution on the way
     *  (4) Check if the other relation holds.
     * @param newResult the generalization result currently constructed
     * @param instIsNewerState indicates if the instance state is the newer state
     * @throws TooExpensiveException if this got too expensive
     */
    private static void handleRelations(LLVMMergeResult newResult, boolean instIsNewerState, Abortion aborter)
    throws TooExpensiveException {
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        LLVMHeuristicState mergeState = (LLVMHeuristicState)newResult.getGeneralizedState();
        final LLVMHeuristicRelationFactory relationFactory = mergeState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        LLVMHeuristicRelationSet ofRelations = new LLVMHeuristicRelationSet(ofState.getRelations());
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(mergeState.getRelations());
        LLVMHeuristicRelationSet added = new LLVMHeuristicRelationSet();
        for (LLVMHeuristicRelation ofRel : ofRelations) {
            // Check if the relation holds in the instance state for some renaming
            boolean notfound = true;
            List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> varMaps =
                LLVMHeuristicStateFactory.findAllRenamings(newResult, ofRel.getVariables(), instIsNewerState, false);
            boolean lost = false;
            if (varMaps.isEmpty()) {
                lost = true;
            }
            for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap : varMaps) {
                aborter.checkAbortion();
                LLVMHeuristicRelation maybeInstRel = ofRel.applySubstitution(varMap);
                // this check needs to be done for all relations to make instantiation sound
                if (instState.getIntegerState().truthValueOfRelation(maybeInstRel, true, aborter) != YNM.YES) {
                    lost = true;
                    continue;
                }
                // only add relation for *one* renaming to avoid relation explosion
                if (true || notfound) {
                    if (LLVMHeuristicStateFactory.directedInequalityHoldsForSmallerOffset(instState, maybeInstRel, aborter)) {
                        continue;
                    }
                    notfound = false;
                    // Build image of this in the merged state, add:
                    LLVMHeuristicRelation newRel =
                        ofRel.applySubstitution(
                            LLVMHeuristicStateFactory.buildMergeSubstitution(newResult, varMap, instIsNewerState)
                        );
                    if (rels.addRelation(mergeState.getIntegerState(), newRel, false, aborter).x) {
                        added.add(newRel);
                    }
                }
            }
            if (lost) {
                // these are costs for the of-state, since we had the relation there, but not in the inst-state
                newResult.addCost(LLVMCost.LOST_RELATION, !instIsNewerState);
                // special case for ref1 + ref2 <= limit - infer ref1' + ref2' <= ref1 + ref2 and try again
                LLVMHeuristicStateFactory.inferIndexRelations(
                    newResult,
                    mergeState,
                    instState,
                    rels,
                    added,
                    ofRelations,
                    ofRel,
                    instIsNewerState,
                    aborter
                );
            }
            if (true || notfound) {
                // if we have a strict directed inequality, check whether its weak version holds
                if (ofRel.getHeuristicRelationType() == LLVMHeuristicRelationType.LT) {
                    LLVMHeuristicRelation weakOfRel = relationFactory.lessThanEquals(ofRel.getLhs(), ofRel.getRhs());
                    for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap : varMaps) {
                        aborter.checkAbortion();
                        LLVMHeuristicRelation maybeWeakInstRel = weakOfRel.applySubstitution(varMap);
                        if (instState.getIntegerState().truthValueOfRelation(maybeWeakInstRel, true, aborter) != YNM.YES) {
                            continue;
                        }
                        // Build image of this in the merged state, add:
                        LLVMHeuristicRelation newRel =
                            weakOfRel.applySubstitution(
                                LLVMHeuristicStateFactory.buildMergeSubstitution(newResult, varMap, instIsNewerState)
                            );
                        if (rels.addRelation(mergeState.getIntegerState(), newRel, false, aborter).x) {
                            added.add(newRel);
                            break;
                        }
                    }
                }
                // additionally, check whether we can infer weaker relations for +/- c patterns
                if (ofRel.isEquation() && !ofRel.isSimple()) {
                    LLVMHeuristicStateFactory.handleOffByConstantPattern(
                        newResult,
                        rels,
                        added,
                        instState,
                        ofRelations,
                        ofRel,
                        instIsNewerState,
                        aborter
                    );
                }
                // if we have an equation x = y op z, check if its weaker overflow safe version holds
                // we only need this when dealing with modulo relation instead of overflow refinements
//                if (ofRel.isEquation() && ofRel.isSimpleArithmeticEquation()) {
//                    Relation weakOfRel = Relation.createOverflowSafeRelation(ofRel);
//                    for (Map<LLVMReference, LLVMReference> varMap : varMaps) {
//                        Relation maybeWeakInstRel = weakOfRel.substituteReferences(varMap);
//                        if (
//                            LLVMIntegerUtils.truthValueOfRelation(instState, maybeWeakInstRel, useSMT, true) != YNM.YES
//                        ) {
//                            continue;
//                        }
//                        // Build image of this in the merged state, add:
//                        Relation newRel =
//                            weakOfRel.substituteReferences(
//                                buildMergeSubstitution(newResult, varMap, instIsNewerState)
//                            );
//                        if (
//                            rels.addRelation(
//                                mergeState,
//                                newRel,
//                                useSMT,
//                                false
//                            )
//                        ) {
//                            added.add(newRel);
//                            break;
//                        }
//                    }
//                }
                // if we have a relation with references which are not used without heap information, we can try to
                // substitute them using equations
                LLVMHeuristicStateFactory.substituteUnusedRefs(
                    newResult,
                    rels,
                    added,
                    ofRel,
                    ofRelations,
                    instIsNewerState,
                    aborter
                );
            }
            /*
             * Special case: we have a relation v1 < v2 in the newer (older) state and ref mappings v1,v3 -> v4 and
             * v2,v3 -> v5 (v3,v1 -> v4 and v3,v2 -> v5). Then we can add the relation v4 <= v5 to the merge-state.
             */
            if (ofRel.isSimple() && ofRel.getHeuristicRelationType() == LLVMHeuristicRelationType.LT) {
                Map<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> refMapping = newResult.getRefMapping();
                LLVMHeuristicVariable v1 = (LLVMHeuristicVariable)ofRel.getLhs();
                LLVMHeuristicVariable v2 = (LLVMHeuristicVariable)ofRel.getRhs();
                Set<LLVMSimpleTerm> v1Partners = newResult.getRefPartners(v1, instIsNewerState);
                Set<LLVMSimpleTerm> v2Partners = newResult.getRefPartners(v2, instIsNewerState);
                for (LLVMSimpleTerm v3 : v1Partners) {
                    if (v2Partners.contains(v3)) {
                        LLVMSimpleTerm v4;
                        LLVMSimpleTerm v5;
                        if (instIsNewerState) {
                            v4 = refMapping.get(new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(v3, v1));
                            v5 = refMapping.get(new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(v3, v2));
                        } else {
                            v4 = refMapping.get(new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(v1, v3));
                            v5 = refMapping.get(new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(v2, v3));
                        }
                        if (v4 != null && v5 != null && !v4.equals(v5)) {
                            LLVMHeuristicRelation newRel = relationFactory.lessThanEquals(v4, v5);
                            if (rels.addRelation(mergeState.getIntegerState(), newRel, false, aborter).x) {
                                added.add(newRel);
                            }
                        }
                    }
                }
            }
        }
        // Special case for keeping the size of heap invariants
        for (Map.Entry<Pair<LLVMSimpleTerm,LLVMSimpleTerm>,LLVMSimpleTerm> entry : newResult.getRefMapping().entrySet()) {
            if (entry.getKey().x instanceof LLVMConstant && entry.getKey().y instanceof LLVMConstant
                && !(entry.getValue() instanceof LLVMConstant)) {
                for (LLVMMemoryRange range : ofState.getMemory().keySet()) {
                    if (range.isPointwise()) continue;
                    if (newResult.getRefPartners(range.getFromRef(), instIsNewerState).isEmpty()) continue;
                    if (newResult.getRefPartners(range.getToRef(), instIsNewerState).isEmpty()) continue;
                    LLVMHeuristicRelation instRel;
                    LLVMHeuristicRelation ofRel;
                    LLVMHeuristicVariable instFromRef;
                    LLVMHeuristicVariable instToRef;
                    BigInteger size = BigInteger.valueOf(IntegerUtils.bitsToBytes(range.getType().size()));
                    if (instIsNewerState) {
                        instFromRef =
                            (LLVMHeuristicVariable) newResult.getRefPartners(range.getFromRef(), true).iterator().next();
                        instToRef =
                            (LLVMHeuristicVariable) newResult.getRefPartners(range.getToRef(), true).iterator().next();
                        ofRel =
                            relationFactory.createAdditionRelation(
                                termFactory.constant(((LLVMConstant)entry.getKey().y).getIntegerValue().multiply(size)),
                                termFactory.sub(range.getToRef(), range.getFromRef()),
                                termFactory.constant(size));
                        instRel =
                            relationFactory.createAdditionRelation(
                                termFactory.constant(((LLVMConstant)entry.getKey().x).getIntegerValue().multiply(size)),
                                termFactory.sub(instToRef, instFromRef),
                                termFactory.constant(size));
                    } else {
                        instFromRef =
                            (LLVMHeuristicVariable) newResult.getRefPartners(range.getFromRef(), false).iterator().next();
                        instToRef =
                            (LLVMHeuristicVariable) newResult.getRefPartners(range.getToRef(), false).iterator().next();
                        ofRel =
                            relationFactory.createAdditionRelation(
                                termFactory.constant(((LLVMConstant)entry.getKey().x).getIntegerValue().multiply(size)),
                                termFactory.sub(range.getToRef(), range.getFromRef()),
                                termFactory.constant(size));
                        instRel =
                            relationFactory.createAdditionRelation(
                                termFactory.constant(((LLVMConstant)entry.getKey().y).getIntegerValue().multiply(size)),
                                termFactory.sub(instToRef, instFromRef),
                                termFactory.constant(size));
                    }
                    if (ofState.getIntegerState().truthValueOfRelation(ofRel, true, aborter) != YNM.YES) {
                        continue;
                    }
                    if (instState.getIntegerState().truthValueOfRelation(instRel, true, aborter) != YNM.YES) {
                        continue;
                    }
                    LLVMHeuristicVariable mergedFromRef =
                        (LLVMHeuristicVariable) newResult.getMergedRef(instFromRef, range.getFromRef(), instIsNewerState);
                    LLVMHeuristicVariable mergedToRef =
                        (LLVMHeuristicVariable) newResult.getMergedRef(instToRef, range.getToRef(), instIsNewerState);
                    LLVMHeuristicRelation newRel =
                        relationFactory.equalTo(
                            termFactory.mult(entry.getValue(), termFactory.constant(size)),
                            termFactory.add(
                                termFactory.sub(mergedToRef, mergedFromRef),
                                termFactory.constant(size)));
                    if (rels.addRelation(mergeState.getIntegerState(), newRel, false, aborter).x) {
                        added.add(newRel);
                    }
                }
            }
        }
        newResult.setGeneralizedState(mergeState.addRelations(added, aborter).x);
    }

    /**
     * Adds relations to the generalized state if both former states satisfy a relation just because of the values,
     * but the generalized state does not anymore.
     * @param newResult The merge result currently under construction.
     */
    private static void handleValueExtensions(LLVMMergeResult newResult, Abortion aborter) {
        LLVMHeuristicState oldState = (LLVMHeuristicState)newResult.getOlderState();
        LLVMHeuristicState newState = (LLVMHeuristicState)newResult.getNewerState();
        LLVMHeuristicState genState = (LLVMHeuristicState)newResult.getGeneralizedState();
        final LLVMHeuristicRelationFactory relationFactory = genState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        Set<LLVMHeuristicRelation> rels = new LinkedHashSet<LLVMHeuristicRelation>();
        // save merges of constant values to non-constant refs (newer,older,merged)
        Set<Triple<LLVMHeuristicConstRef, LLVMHeuristicConstRef, LLVMHeuristicVariable>> constMerges =
            new LinkedHashSet<Triple<LLVMHeuristicConstRef, LLVMHeuristicConstRef, LLVMHeuristicVariable>>();
        for (
            Map.Entry<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> entry :
                newResult.getRefMapping().entrySet()
        ) {
            aborter.checkAbortion();
            Pair<LLVMSimpleTerm, LLVMSimpleTerm> pair = entry.getKey();
            LLVMHeuristicVariable genRef = (LLVMHeuristicVariable)entry.getValue();
            if (
                ((LLVMHeuristicVariable)pair.x).isConcrete()
                && ((LLVMHeuristicVariable)pair.y).isConcrete()
                && !genRef.isConcrete()
            ) {
                constMerges.add(
                    new Triple<LLVMHeuristicConstRef, LLVMHeuristicConstRef, LLVMHeuristicVariable>(
                        (LLVMHeuristicConstRef)pair.x,
                        (LLVMHeuristicConstRef)pair.y,
                        genRef
                    )
                );
            }
            ImmutableMap<LLVMHeuristicVariable, LLVMValue> oldVals = oldState.getValues();
            ImmutableMap<LLVMHeuristicVariable, LLVMValue> newVals = newState.getValues();
            ImmutableMap<LLVMHeuristicVariable, LLVMValue> genVals = genState.getValues();
            if (LLVMHeuristicState.getValue((LLVMHeuristicVariable)pair.y, oldVals) instanceof AbstractFloat
                || LLVMHeuristicState.getValue((LLVMHeuristicVariable)pair.x, newVals) instanceof AbstractFloat) {
                continue;
            }
            AbstractBoundedInt oldVal =
                LLVMHeuristicState.getValue((LLVMHeuristicVariable)pair.y, oldVals).getThisAsAbstractBoundedInt();
            AbstractBoundedInt newVal =
                LLVMHeuristicState.getValue((LLVMHeuristicVariable)pair.x, newVals).getThisAsAbstractBoundedInt();
            AbstractBoundedInt genVal = LLVMHeuristicState.getValue(genRef, genVals).getThisAsAbstractBoundedInt();
            IntervalBound oldUp = oldVal.getUpper();
            IntervalBound newUp = newVal.getUpper();
            IntervalBound genUp = genVal.getUpper();
            IntervalBound oldLow = oldVal.getLower();
            IntervalBound newLow = newVal.getLower();
            IntervalBound genLow = genVal.getLower();
            if (newUp.isFinite() && oldUp.isFinite() && (genUp.compareTo(newUp) > 0 || genUp.compareTo(oldUp) > 0)) {
                // upper bound has been extended
                for (Map.Entry<LLVMHeuristicVariable, LLVMValue> newValEntry : newVals.entrySet()) {
                    LLVMHeuristicVariable otherNewRef = newValEntry.getKey();
                    if (newValEntry.getValue() instanceof AbstractFloat) continue;
                    IntervalBound otherNewLow = newValEntry.getValue().getThisAsAbstractBoundedInt().getLower();
                    if (newUp.compareTo(otherNewLow) < 0) {
                        for (LLVMSimpleTerm oldPartner : newResult.getRefPartners(otherNewRef, false)) {
                            IntervalBound otherOldLow =
                                LLVMHeuristicState.getValue(
                                    (LLVMHeuristicVariable)oldPartner,
                                    oldVals
                                ).getThisAsAbstractBoundedInt().getLower();
                            LLVMHeuristicVariable otherGenRef =
                                (LLVMHeuristicVariable)newResult.getMergedRef(otherNewRef, oldPartner, true);
                            IntervalBound otherGenLow =
                                LLVMHeuristicState.getValue(
                                    otherGenRef,
                                    genVals
                                ).getThisAsAbstractBoundedInt().getLower();
                            if (oldUp.compareTo(otherOldLow) < 0 && genUp.compareTo(otherGenLow) >= 0) {
                                rels.add(relationFactory.lessThan(genRef, otherGenRef));
                            } else if (oldUp.compareTo(otherOldLow) <= 0 && genUp.compareTo(otherGenLow) > 0) {
                                rels.add(relationFactory.lessThanEquals(genRef, otherGenRef));
                            }
                        }
                    } else if (newUp.compareTo(otherNewLow) == 0) {
                        for (LLVMSimpleTerm oldPartner : newResult.getRefPartners(otherNewRef, false)) {
                            IntervalBound otherOldLow =
                                LLVMHeuristicState.getValue(
                                    (LLVMHeuristicVariable)oldPartner,
                                    oldVals
                                ).getThisAsAbstractBoundedInt().getLower();
                            LLVMHeuristicVariable otherGenRef =
                                (LLVMHeuristicVariable)newResult.getMergedRef(otherNewRef, oldPartner, true);
                            if (
                                oldUp.compareTo(otherOldLow) <= 0
                                && genUp.compareTo(
                                    LLVMHeuristicState.getValue(
                                        otherGenRef,
                                        genVals
                                    ).getThisAsAbstractBoundedInt().getLower()
                                ) > 0
                            ) {
                                rels.add(relationFactory.lessThanEquals(genRef, otherGenRef));
                            }
                        }
                    }
                }
            }
            if (
                newLow.isFinite()
                && oldLow.isFinite()
                && (genLow.compareTo(newLow) < 0 || genLow.compareTo(oldLow) < 0)
            ) {
                // lower bound has been extended
                for (Map.Entry<LLVMHeuristicVariable, LLVMValue> newValEntry : newVals.entrySet()) {
                    LLVMHeuristicVariable otherNewRef = newValEntry.getKey();
                    if (newValEntry.getValue() instanceof AbstractFloat) continue;
                    IntervalBound otherNewUp = newValEntry.getValue().getThisAsAbstractBoundedInt().getUpper();
                    if (newLow.compareTo(otherNewUp) > 0) {
                        for (LLVMSimpleTerm oldPartner : newResult.getRefPartners(otherNewRef, false)) {
                            IntervalBound otherOldUp =
                                LLVMHeuristicState.getValue(
                                    (LLVMHeuristicVariable)oldPartner,
                                    oldVals
                                ).getThisAsAbstractBoundedInt().getUpper();
                            LLVMHeuristicVariable otherGenRef =
                                (LLVMHeuristicVariable)newResult.getMergedRef(otherNewRef, oldPartner, true);
                            IntervalBound otherGenUp =
                                LLVMHeuristicState.getValue(
                                    otherGenRef,
                                    genVals
                                ).getThisAsAbstractBoundedInt().getUpper();
                            if (oldLow.compareTo(otherOldUp) > 0 && genLow.compareTo(otherGenUp) <= 0) {
                                rels.add(relationFactory.lessThan(otherGenRef, genRef));
                            } else if (oldLow.compareTo(otherOldUp) >= 0 && genLow.compareTo(otherGenUp) < 0) {
                                rels.add(relationFactory.lessThanEquals(otherGenRef, genRef));
                            }
                        }
                    } else if (newLow.compareTo(otherNewUp) == 0) {
                        for (LLVMSimpleTerm oldPartner : newResult.getRefPartners(otherNewRef, false)) {
                            IntervalBound otherOldUp =
                                LLVMHeuristicState.getValue(
                                    (LLVMHeuristicVariable)oldPartner,
                                    oldVals
                                ).getThisAsAbstractBoundedInt().getUpper();
                            LLVMHeuristicVariable otherGenRef =
                                (LLVMHeuristicVariable)newResult.getMergedRef(otherNewRef, oldPartner, true);
                            if (
                                oldLow.compareTo(otherOldUp) >= 0
                                && genLow.compareTo(
                                    LLVMHeuristicState.getValue(
                                        otherGenRef,
                                        genVals
                                    ).getThisAsAbstractBoundedInt().getUpper()
                                ) < 0
                            ) {
                                rels.add(relationFactory.lessThanEquals(otherGenRef, genRef));
                            }
                        }
                    }
                }
            }
        }
        for (Triple<LLVMHeuristicConstRef, LLVMHeuristicConstRef, LLVMHeuristicVariable> constMerge1 : constMerges) {
            for (Triple<LLVMHeuristicConstRef, LLVMHeuristicConstRef, LLVMHeuristicVariable> constMerge2 : constMerges) {
                if (constMerge1.equals(constMerge2)) {
                    continue;
                }
                // we have two different merges of constant values - check whether they have the same difference in
                // both states and if so, add this difference as a relation
                BigInteger diffNew = constMerge1.x.getIntegerValue().subtract(constMerge2.x.getIntegerValue());
                BigInteger diffOld = constMerge1.y.getIntegerValue().subtract(constMerge2.y.getIntegerValue());
                if (diffNew.compareTo(diffOld) == 0) {
                    if (Globals.useAssertions) {
                        assert (diffNew.compareTo(BigInteger.ZERO) != 0) :
                            "We have two entries for the same merge - how is this possible?";
                    }
                    // prefer addition relation
                    BigInteger diff;
                    LLVMHeuristicVariable biggerRef;
                    LLVMHeuristicVariable smallerRef;
                    if (diffNew.compareTo(BigInteger.ZERO) < 0) {
                        diff = diffNew.negate();
                        biggerRef = constMerge2.z;
                        smallerRef = constMerge1.z;
                    } else {
                        diff = diffNew;
                        biggerRef = constMerge1.z;
                        smallerRef = constMerge2.z;
                    }
                    rels.add(relationFactory.createAdditionRelation(biggerRef, smallerRef, termFactory.constant(diff)));
                }
            }
        }
        newResult.setGeneralizedState(genState.addRelations(rels, aborter).x);
    }

    /**
     * Fills the variable function for one call stack entry. To handle the symmetric cases, this method should be
     * called twice with different boolean values.
     * @param newResult The merge result under construction.
     * @param genVarFunc The variable function under construction.
     * @param instVars One variable function.
     * @param ofVars Another variable function.
     * @param instIsNewerState Flag indicating whether instState is the newer state.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @throws TooExpensiveException If some variable entries don't match after merging.
     */
    private static void handleVariableFunctionInCallStack(
        LLVMMergeResult newResult,
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> genVarFunc,
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> instVars,
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> ofVars,
        boolean instIsNewerState,
        boolean aggressive,
        boolean fastConvergence
    ) throws TooExpensiveException {
        final boolean useBoundedIntegers = newResult.getGeneralizedState().getStrategyParamters().useBoundedIntegers;
        for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> ofVarMapEntry : ofVars.entrySet()) {
            String varName = ofVarMapEntry.getKey();
            ImmutablePair<LLVMSymbolicVariable, LLVMType> ofVarEntry = ofVarMapEntry.getValue();
            if (instVars.containsKey(varName)) {
                ImmutablePair<LLVMSymbolicVariable, LLVMType> instVarEntry = instVars.get(varName);
                if (!instVarEntry.y.equals(ofVarEntry.y)) {
                    throw new TooExpensiveException("Variables with the same name have different types!");
                }
                if (genVarFunc.containsKey(varName)) {
                    // we have already seen this
                    continue;
                }
                LLVMHeuristicVariable instVarRef = (LLVMHeuristicVariable)instVarEntry.x;
                LLVMHeuristicVariable ofVarRef = (LLVMHeuristicVariable)ofVarEntry.x;
                boolean unsigned;
                if (useBoundedIntegers) {
                    unsigned =
                        newResult.getOfState(instIsNewerState).getModule().getUnsignedBitvectorVariables().contains(varName);
                } else {
                    unsigned =
                        newResult.getOfState(instIsNewerState).getModule().getUnsignedUnboundedVariables().contains(varName);
                }
                IntegerType intType = instVarEntry.y.getIntegerType(unsigned, useBoundedIntegers);
                LLVMHeuristicVariable mergedRef =
                    LLVMHeuristicStateFactory.mergeReferences(
                        newResult,
                        instVarRef,
                        ofVarRef,
                        intType,
                        instIsNewerState,
                        aggressive,
                        fastConvergence
                    );
                genVarFunc.put(varName, new ImmutablePair<LLVMSymbolicVariable, LLVMType>(mergedRef, instVarEntry.y));
            } else {
                // This variable is only defined in one state:
                throw new TooExpensiveException("Lost variable!");
            }
        }
    }

    /**
     * Adds suitably general values for all variables to the generalization result. If a variable from the progenitor
     * state does not occur in the instance state, generalization is not possible (a TooExpensiveExcpetion is thrown -
     * in theory, one could merge with an arbitrary value, but in most cases this leads to unintended merge behavior
     * with early states before all variables have been initialized).
     * @param newResult The generalization result currently constructed.
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @throws TooExpensiveException If this got too expensive...
     */
    private static void handleVariables(LLVMMergeResult newResult, boolean instIsNewerState, boolean aggressive, boolean fastConvergence, Abortion aborter)
    throws TooExpensiveException {
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        final boolean useBoundedIntegers = instState.getStrategyParamters().useBoundedIntegers;
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> instVars = instState.getProgramVariables();
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> ofVars = ofState.getProgramVariables();
        for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> ofVarMapEntry : ofVars.entrySet()) {
            String varName = ofVarMapEntry.getKey();
            ImmutablePair<LLVMSymbolicVariable, LLVMType> ofVarEntry = ofVarMapEntry.getValue();
            if (instVars.containsKey(varName)) {
                ImmutablePair<LLVMSymbolicVariable, LLVMType> instVarEntry = instVars.get(varName);
                LLVMHeuristicVariable instRef = (LLVMHeuristicVariable)instVarEntry.x;
                // we do not want to merge concrete boolean values to something more unknown as there are only two
                // possible values
                if (instVarEntry.y.isBooleanType()
                    && (instRef.isConcrete() || ((LLVMHeuristicVariable)ofVarEntry.x).isConcrete())
                    && !ofVarEntry.x.equals(instRef)
                    && !aggressive)
                {
                    throw new TooExpensiveException(
                        "Trying to merge a concrete boolean value to something more unknown!"
                    );
                }
                if (!instVarEntry.y.equals(ofVarEntry.y)) {
                    throw new TooExpensiveException("Variables with the same name have different types!");
                }
                if (instVarEntry.y.isPointerType() && ((LLVMPointerType)instVarEntry.y).pointsToStruct()) {
                    if (!aggressive) {
                        if (instState.findStructInvariantForStartRef(instVarEntry.x) != null && ofState.findStructInvariantForStartRef(ofVarEntry.x) == null) {
                            throw new TooExpensiveException("Losing knowledge for struct invariant!");
                        }
                    }
                }
                boolean unsigned;
                if (useBoundedIntegers) {
                    unsigned =
                        newResult.getOfState(instIsNewerState).getModule().getUnsignedBitvectorVariables().contains(varName);
                } else {
                    unsigned =
                        newResult.getOfState(instIsNewerState).getModule().getUnsignedUnboundedVariables().contains(varName);
                }
                IntegerType intType = instVarEntry.y.getIntegerType(unsigned, useBoundedIntegers);
                // the following two operations must be done in this order since newResult is changed in the first one
                LLVMHeuristicVariable mergedRef =
                    LLVMHeuristicStateFactory.mergeReferences(
                        newResult,
                        instRef,
                        (LLVMHeuristicVariable)ofVarEntry.x,
                        intType,
                        instIsNewerState,
                        aggressive,
                        fastConvergence
                    );
                newResult.setGeneralizedState(
                    newResult.getGeneralizedState().setProgramVariable(varName, mergedRef, ofVarEntry.y)
                );
            } else {
                // This variable is only defined in the progenitor state:
                throw new TooExpensiveException("Lost variable");
            }
        }
    }

    /**
     * @param rels The relations.
     * @param x A reference.
     * @param y Another reference.
     * @param offset An already known offset.
     * @param positive Are we looking for positive or negative offsets?
     * @return If the relations imply that x + c = y for some constant c whose sign is specified by the boolean flag,
     *         then offset + c is returned. Null otherwise.
     */
    private static BigInteger hasKnownOffset(
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicVariable x,
        LLVMHeuristicVariable y,
        BigInteger offset,
        boolean positive
    ) {
        for (LLVMHeuristicRelation rel : rels.getEquations()) {
            Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> pattern = rel.toOffByConstantPattern();
            if (pattern == null) {
                continue;
            }
            LLVMHeuristicVariable forX;
            LLVMHeuristicVariable forY;
            BigInteger add;
            if (positive) {
                if (pattern.z.compareTo(BigInteger.ZERO) < 0) {
                    forX = pattern.y;
                    forY = pattern.x;
                    add = pattern.z.negate();
                } else {
                    forX = pattern.x;
                    forY = pattern.y;
                    add = pattern.z;
                }
            } else {
                if (pattern.z.compareTo(BigInteger.ZERO) < 0) {
                    forX = pattern.x;
                    forY = pattern.y;
                    add = pattern.z;
                } else {
                    forX = pattern.y;
                    forY = pattern.x;
                    add = pattern.z.negate();
                }
            }
            if (!forX.equals(x)) {
                continue;
            }
            if (forY.equals(y)) {
                return offset.add(add);
            } else {
                BigInteger res = LLVMHeuristicStateFactory.hasKnownOffset(rels, forY, y, offset.add(add), positive);
                if (res != null) {
                    return res;
                }
            }
        }
        return null;
    }

    /**
     * @param newResult The merge result under construction.
     * @param mergeState The merged state.
     * @param instState The inst-state
     * @param rels The relations of the merged state.
     * @param added The really added relations.
     * @param ofRelations The relations of the of-state.
     * @param ofRel One relation of the of-state.
     * @param instIsNewerState Is the inst-state the newer state?
     */
    private static void inferIndexRelations(
        LLVMMergeResult newResult,
        LLVMHeuristicState mergeState,
        LLVMHeuristicState instState,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicRelationSet added,
        LLVMHeuristicRelationSet ofRelations,
        LLVMHeuristicRelation ofRel,
        boolean instIsNewerState,
        Abortion aborter
    ) {
        if (!ofRel.isDirectedInequality()) {
            return;
        }
        final LLVMHeuristicRelationFactory relationFactory = mergeState.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        LLVMHeuristicTerm lhs = ofRel.getLhs();
        LLVMHeuristicTerm rhs = ofRel.getRhs();
        if (rhs instanceof LLVMHeuristicVarRef && lhs.isSumOfTwoDifferentVariables()) {
            Iterator<? extends LLVMHeuristicVariable> it = lhs.getVariables(false).iterator();
            // stores ref pairs know to be less than rhs and a flag indicating whether an inequality was
            // used to infer this pair
            Set<Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>> less =
                new LinkedHashSet<Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>>();
            Set<Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>> lastLess =
                new LinkedHashSet<Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>>();
            Set<Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>> newLess =
                new LinkedHashSet<Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>>();
            newLess.add(new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(it.next(), it.next(), false));
            while (!newLess.isEmpty()) {
                aborter.checkAbortion();
                less.addAll(newLess);
                lastLess.clear();
                lastLess.addAll(newLess);
                newLess.clear();
                for (LLVMHeuristicRelation otherOfRel : ofRelations.getRelationsWithoutUndirectedInequalities()) {
                    for (Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean> triple : lastLess) {
                        if (otherOfRel.isEquation()) {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear =
                                otherOfRel.getLhs().toLinear();
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherRhsLinear =
                                otherOfRel.getRhs().toLinear();
                            if (
                                !(
                                    otherLhsLinear.x instanceof LLVMHeuristicVarRef
                                    && otherRhsLinear.x instanceof LLVMHeuristicVarRef
                                    && otherLhsLinear.z.compareTo(BigInteger.ONE) == 0
                                    && otherRhsLinear.z.compareTo(BigInteger.ONE) == 0
                                )
                            ) {
                                continue;
                            }
                            BigInteger offsetLeft = otherLhsLinear.y.subtract(otherRhsLinear.y);
                            if (
                                triple.x.equals(otherLhsLinear.x)
                                && offsetLeft.compareTo(BigInteger.ZERO) <= 0
                            ) {
                                newLess.add(
                                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(
                                        (LLVMHeuristicVariable)otherRhsLinear.x,
                                        triple.y,
                                        triple.z
                                    )
                                );
                            } else if (
                                triple.x.equals(otherRhsLinear.x)
                                && offsetLeft.compareTo(BigInteger.ZERO) >= 0
                            ) {
                                newLess.add(
                                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(
                                        (LLVMHeuristicVariable)otherLhsLinear.x,
                                        triple.y,
                                        triple.z
                                    )
                                );
                            } else if (
                                triple.y.equals(otherLhsLinear.x)
                                && offsetLeft.compareTo(BigInteger.ZERO) <= 0
                            ) {
                                newLess.add(
                                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(
                                        triple.x,
                                        (LLVMHeuristicVariable)otherRhsLinear.x,
                                        triple.z
                                    )
                                );
                            } else if (
                                triple.y.equals(otherRhsLinear.x)
                                && offsetLeft.compareTo(BigInteger.ZERO) >= 0
                            ) {
                                newLess.add(
                                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(
                                        triple.x,
                                        (LLVMHeuristicVariable)otherLhsLinear.x,
                                        triple.z
                                    )
                                );
                            }
                        } else {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear =
                                otherOfRel.getLhs().toLinear();
                            if (
                                !(
                                    otherLhsLinear.x instanceof LLVMHeuristicVarRef
                                    && otherLhsLinear.z.compareTo(BigInteger.ONE) == 0
                                    && otherLhsLinear.y.compareTo(BigInteger.ZERO) >= 0
                                )
                            ) {
                                continue;
                            }
                            LLVMHeuristicTerm otherRhs = otherOfRel.getRhs();
                            if (triple.x.equals(otherRhs)) {
                                newLess.add(
                                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(
                                        (LLVMHeuristicVariable)otherLhsLinear.x,
                                        triple.y,
                                        true
                                    )
                                );
                            } else if (triple.y.equals(otherRhs)) {
                                newLess.add(
                                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean>(
                                        triple.x,
                                        (LLVMHeuristicVariable)otherLhsLinear.x,
                                        true
                                    )
                                );
                            }
                        }
                    }
                }
            }
            for (Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, Boolean> triple : less) {
                if (!triple.z) {
                    continue;
                }
                LLVMHeuristicRelation inferred =
                    relationFactory.lessThanEquals(termFactory.add(triple.x, triple.y), rhs);
                List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> varMapsForInferred =
                    LLVMHeuristicStateFactory.findAllRenamings(
                        newResult,
                        inferred.getVariables(),
                        instIsNewerState,
                        false
                    );
                for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap : varMapsForInferred) {
                    LLVMHeuristicRelation maybeInstRel = inferred.applySubstitution(varMap);
                    // this check needs to be done for all relations to make instantiation sound
                    if (instState.getIntegerState().truthValueOfRelation(maybeInstRel, true, aborter) != YNM.YES) {
                        continue;
                    }
                    // Build image of this in the merged state, add:
                    LLVMHeuristicRelation newRel =
                        inferred.applySubstitution(
                            LLVMHeuristicStateFactory.buildMergeSubstitution(newResult, varMap, instIsNewerState)
                        );
                    if (rels.addRelation(mergeState.getIntegerState(), newRel, false, aborter).x) {
                        added.add(newRel);
                    }
                }
            }
        }
    }

    /**
     * Tries to infer the given relation from the of-state in the inst-state by some renaming. In case the inference is
     * successful, we try to add a renamed version of the inferred relation to the relation set rels.
     * @param newResult The generalization result under construction.
     * @param rels The new relations.
     * @param added The really added relations.
     * @param instState The inst-state.
     * @param instRelations The relations in the inst-state.
     * @param ofRel The relation from the of-state to infer in the inst-state.
     * @param instIsNewerState Flag indicating whether the inst-state is the newer state.
     * @return True if we added a new relation to the RelationSet. False otherwise.
     */
    private static boolean inferRelation(
        LLVMMergeResult newResult,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicRelationSet added,
        LLVMHeuristicState instState,
        ImmutableSet<LLVMHeuristicRelation> instRelations,
        LLVMHeuristicRelation ofRel,
        boolean instIsNewerState,
        Abortion aborter
    ) {
        boolean changed = false;
        for (
            Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap :
                LLVMHeuristicStateFactory.findAllRenamings(
                    newResult,
                    ofRel.getVariables(),
                    instIsNewerState,
                    false
                )
        ) {
            LLVMHeuristicRelation instRelCandidate = ofRel.applySubstitution(varMap);
            if (instState.getIntegerState().truthValueOfRelation(instRelCandidate, true, aborter) == YNM.YES) {
                LLVMHeuristicRelation newRel =
                    ofRel.applySubstitution(
                        LLVMHeuristicStateFactory.buildMergeSubstitution(newResult, varMap, instIsNewerState)
                    );
                if (
                    rels.addRelation(
                        ((LLVMHeuristicState)newResult.getGeneralizedState()).getIntegerState(),
                        newRel,
                        false,
                        aborter
                    ).x
                ) {
                    added.add(newRel);
                    changed = true;
                } else {
                    return changed;
                }
            }
        }
        return changed;
    }

    /**
     * @param newResult The generalization result currently under construction.
     * @param newExpr An expression in the newer state.
     * @param oldExpr An expression in the older state.
     * @return A merged expression in case all references in both specified expressions are suitably merged and both
     *         expressions are the same after merging. Null otherwise.
     */
    private static LLVMHeuristicTerm isExprMerged(
        LLVMMergeResult newResult,
        LLVMHeuristicTerm newExpr,
        LLVMHeuristicTerm oldExpr
    ) {
        if (newExpr instanceof LLVMHeuristicVarRef) {
            if (oldExpr instanceof LLVMHeuristicVarRef) {
                return
                    (LLVMHeuristicTerm)
                        newResult.getMergedRef((LLVMHeuristicVariable)newExpr, (LLVMHeuristicVariable)oldExpr, true);
            } else {
                return null;
            }
        } else if (newExpr instanceof LLVMHeuristicConstRef) {
            if (oldExpr instanceof LLVMHeuristicConstRef) {
                // TODO for now, we do not consider merged constants - should we?
                return newExpr.equals(oldExpr) ? newExpr : null;
            } else {
                return null;
            }
        } else if (newExpr instanceof LLVMHeuristicOperation) {
            if (oldExpr instanceof LLVMHeuristicOperation) {
                LLVMHeuristicOperation newOp = (LLVMHeuristicOperation)newExpr;
                LLVMHeuristicOperation oldOp = (LLVMHeuristicOperation)oldExpr;
                if (newOp.getOperation() != oldOp.getOperation()) {
                    return null;
                }
                LLVMHeuristicTerm mergedLhs =
                    LLVMHeuristicStateFactory.isExprMerged(newResult, newOp.getLhs(), oldOp.getLhs());
                if (mergedLhs == null) {
                    return null;
                }
                LLVMHeuristicTerm mergedRhs =
                    LLVMHeuristicStateFactory.isExprMerged(newResult, newOp.getRhs(), oldOp.getRhs());
                if (mergedRhs == null) {
                    return null;
                }
                return
                    ((LLVMHeuristicState)newResult.getGeneralizedState()).getRelationFactory().getTermFactory().create(
                        newOp.getOperation(),
                        mergedLhs,
                        mergedRhs
                    );
            } else {
                return null;
            }
        } else {
            throw new IllegalStateException("Found an expression which is neither a reference nor an operation!");
        }
    }

    /**
     * @param newResult The generalization result currently under construction.
     * @param instRef Some reference in the instance state.
     * @param ofRef Some reference in the progenitor state.
     * @param type The integer type of the values.
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @return A reference representing the merge of instRef and ofRef, with all needed value/dereferencing information
     *         already put into the merged state.
     * @throws TooExpensiveException If this got too expensive.
     */
    private static LLVMHeuristicVariable mergeReferences(
        LLVMMergeResult newResult,
        LLVMHeuristicVariable instRef,
        LLVMHeuristicVariable ofRef,
        IntegerType type,
        boolean instIsNewerState,
        boolean aggressive,
        boolean fastConvergence
    ) throws TooExpensiveException {
        // Look at the cache first, maybe we are already done:
        if (newResult.refPairAlreadyMerged(instRef, ofRef, instIsNewerState)) {
            return (LLVMHeuristicVariable)newResult.getMergedRef(instRef, ofRef, instIsNewerState);
        }
        // Prepare the instruments
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        // First, look at the actual integer value:
        LLVMValue instVal = instState.getValue(instRef);
        LLVMValue ofVal = ofState.getValue(ofRef);
        if (Globals.useAssertions) {
            assert (instVal != null && ofVal != null) : "Trying to merge NULL values.";
        }
        // Determine integer type of the merged value
        AbstractBoundedInt instInt = null;
        AbstractBoundedInt ofInt = null;
        if (!(instVal instanceof AbstractFloat) && !(ofVal instanceof AbstractFloat)) {
            instInt = instVal.getThisAsAbstractBoundedInt();
            ofInt = ofVal.getThisAsAbstractBoundedInt();
        }
        IntegerType mergedType;
        final boolean useBoundedIntegers = instState.getStrategyParamters().useBoundedIntegers;
        // When using bounded integers, we do not want to merge negative values to non-negative values as this would
        // lead to an expensive loss of information for unsigned comparisons
        if (useBoundedIntegers && !aggressive
            && ((instInt.isNegative() && ofInt.isNonNegative()) || (instInt.isNonNegative() && ofInt.isNegative())))
        {
            throw new TooExpensiveException(
                "Trying to merge a negative value with a non-negative value!"
            );
        }
        if (instVal instanceof AbstractFloat && ofVal instanceof AbstractFloat) {
            mergedType = IntegerType.UNBOUND;
        } else {
            if (useBoundedIntegers) {
                mergedType = type;
            } else {
                mergedType =
                    instInt.isPositive() && ofInt.isPositive() ?
                        IntegerType.UNBOUND_POSITIVE :
                            instInt.isNonNegative() && ofInt.isNonNegative() ?
                                IntegerType.UNBOUND_NON_NEGATIVE :
                                    IntegerType.UNBOUND;
            }
        }
        LLVMValue mergedValue =
            LLVMHeuristicStateFactory.mergeValues(newResult, instVal, ofVal, mergedType, instIsNewerState, fastConvergence);
        LLVMHeuristicVariable mergedRef = (LLVMHeuristicVariable)newResult.mergeRefs(instRef, ofRef, instIsNewerState);
        if (mergedValue.isIntLiteral() && !(mergedRef instanceof LLVMHeuristicConstRef)) {
            mergedRef = instState.getRelationFactory().getTermFactory().constant(mergedValue.getIntLiteralValue());
            newResult.getRefMapping().put(
                instIsNewerState ?
                    new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(instRef, ofRef) :
                        new Pair<LLVMSimpleTerm, LLVMSimpleTerm>(ofRef, instRef),
                mergedRef
            );
        }
        newResult.setGeneralizedState(
            ((LLVMHeuristicState)newResult.getGeneralizedState()).setValue(mergedRef, mergedValue)
        );
        return mergedRef;
    }

    /**
     * @param newResult The generalization result currently constructed.
     * @param instVal Some value in the instance state.
     * @param ofVal Some value in the progenitor state.
     * @param type The integer type of the values.
     * @param instIsNewerState Indicates if the instance state is the newer state.
     * @param fastConvergence Do we think that for this merge, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @return A value representing both instVal and ofVal.
     * @throws TooExpensiveException If this got too expensive.
     */
    private static LLVMValue mergeValues(
        LLVMMergeResult newResult,
        LLVMValue instVal,
        LLVMValue ofVal,
        IntegerType type,
        boolean instIsNewerState,
        boolean fastConvergence
    ) throws TooExpensiveException {
        AbstractNumberMergeResult variableMergeResult = null;
        if (instVal instanceof AbstractFloat && ofVal instanceof AbstractFloat) {
            if (instIsNewerState) {
                variableMergeResult = ((AbstractFloat)ofVal).merge((AbstractFloat)instVal);
            } else{
                variableMergeResult = ((AbstractFloat)instVal).merge((AbstractFloat)ofVal);
            }
        } else {
            AbstractBoundedInt instInt = instVal.getThisAsAbstractBoundedInt();
            AbstractBoundedInt ofInt = ofVal.getThisAsAbstractBoundedInt();
            int mergeToExtremeValCountThreshold = 
                    fastConvergence ?   MERGE_TO_EXTREME_VALUE_COUNT_THRESHOLD_FAST_CONVERGENCE :
                                        MERGE_TO_EXTREME_VALUE_COUNT_THRESHOLD_NORMAL_CONVERGENCE;
            if (instIsNewerState) {
                variableMergeResult = ofInt.merge(instInt, true, type, mergeToExtremeValCountThreshold);
            } else{
                variableMergeResult = instInt.merge(ofInt, true, type, mergeToExtremeValCountThreshold);
            }
        }
        // Note the differences:
        newResult.addCost(LLVMCost.convertJBCToLLVMCost(variableMergeResult.getVarAtoMerged()), instIsNewerState);
        newResult.addCost(LLVMCost.convertJBCToLLVMCost(variableMergeResult.getVarBtoMerged()), !instIsNewerState);
        /*
         * Handle cost that was only added because widening was enforced to
         * get a finite graph. As this is irrelevant in the case of an
         * instance computation, we just add this to the case from the
         * newer to the merged state:
         */
        CostType wideningCost = variableMergeResult.getEnforcedWideningCost();
        if (wideningCost != null) {
            newResult.addCost(LLVMCost.convertJBCToLLVMCost(wideningCost), true);
        }
        return variableMergeResult.getMergedVariable();
//        if (instVal instanceof LLVMTrapValue) {
//            if (ofVal instanceof LLVMTrapValue) {
//                ImmutablePair<LLVMHeuristicVariable, BigInteger> instDep = ((LLVMTrapValue)instVal).getAssociationDependency();
//                ImmutablePair<LLVMHeuristicVariable, BigInteger> ofDep = ((LLVMTrapValue)ofVal).getAssociationDependency();
//                res =
//                    new LLVMTrapValue(
//                        res,
//                        new ImmutablePair<LLVMHeuristicVariable, BigInteger>(
//                            LLVMHeuristicStateFactory.mergeReferences(newResult, instDep.x, ofDep.x, type, instIsNewerState, params),
//                            instDep.y.max(ofDep.y)
//                        )
//                    );
//            } else {
//                ImmutablePair<LLVMHeuristicVariable, BigInteger> instDep = ((LLVMTrapValue)instVal).getAssociationDependency();
//                Set<LLVMHeuristicVariable> partners = newResult.getRefPartners(instDep.x, !instIsNewerState);
//                LLVMHeuristicVariable mergedRef = null;
//                if (partners.isEmpty()) {
//                    boolean notFound = true;
//                    for (
//                        Map.Entry<String, ImmutablePair<LLVMHeuristicVariable, BasicType>> entry :
//                            newResult.getInstState(instIsNewerState).getProgramVariables().entrySet()
//                    ) {
//                        if (entry.getValue().x.equals(instDep.x)) {
//                            mergedRef =
//                                LLVMHeuristicStateFactory.mergeReferences(
//                                    newResult,
//                                    instDep.x,
//                                    newResult.getOfState(instIsNewerState).getSymbolicVariableForProgramVariable(entry.getKey()),
//                                    type,
//                                    instIsNewerState,
//                                    params
//                                );
//                            notFound = false;
//                            break;
//                        }
//                    }
//                    if (notFound) {
//                        throw new IllegalStateException("Found association dependency, but the reference is not used!");
//                    }
//                } else {
//                    // just take any
//                    mergedRef = newResult.getMergedRef(instDep.x, partners.iterator().next(), instIsNewerState);
//                }
//                res =
//                    new LLVMTrapValue(res, new ImmutablePair<LLVMHeuristicVariable, BigInteger>(mergedRef, instDep.y));
//            }
//        } else if (ofVal instanceof LLVMTrapValue) {
//            ImmutablePair<LLVMHeuristicVariable, BigInteger> ofDep = ((LLVMTrapValue)ofVal).getAssociationDependency();
//            Set<LLVMHeuristicVariable> partners = newResult.getRefPartners(ofDep.x, instIsNewerState);
//            LLVMHeuristicVariable mergedRef = null;
//            if (partners.isEmpty()) {
//                boolean notFound = true;
//                for (
//                    Map.Entry<String, ImmutablePair<LLVMHeuristicVariable, BasicType>> entry :
//                        newResult.getOfState(instIsNewerState).getProgramVariables().entrySet()
//                ) {
//                    if (entry.getValue().x.equals(ofDep.x)) {
//                        mergedRef =
//                            LLVMHeuristicStateFactory.mergeReferences(
//                                newResult,
//                                newResult.getInstState(instIsNewerState).getSymbolicVariableForProgramVariable(entry.getKey()),
//                                ofDep.x,
//                                type,
//                                instIsNewerState,
//                                params
//                            );
//                        notFound = false;
//                        break;
//                    }
//                }
//                if (notFound) {
//                    throw new IllegalStateException("Found association dependency, but the reference is not used!");
//                }
//            } else {
//                // just take any
//                mergedRef = newResult.getMergedRef(ofDep.x, partners.iterator().next(), instIsNewerState);
//            }
//            res =
//                new LLVMTrapValue(res, new ImmutablePair<LLVMHeuristicVariable, BigInteger>(mergedRef, ofDep.y));
//        }
//        return res;
    }

    /**
     * @param newResult The generalization result under construction.
     * @param rels The relations for the merged state.
     * @param added The really added relations.
     * @param ofRel The relation to check for substitution possibilities.
     * @param ofRelations The relations in the of-state.
     * @param instIsNewerState Is the inst-state the newer state?
     */
    private static void substituteUnusedRefs(
        LLVMMergeResult newResult,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicRelationSet added,
        LLVMHeuristicRelation ofRel,
        LLVMHeuristicRelationSet ofRelations,
        boolean instIsNewerState,
        Abortion aborter
    ) {
        LLVMHeuristicState ofState = (LLVMHeuristicState)newResult.getOfState(instIsNewerState);
        Set<LLVMHeuristicVariable> unusedOfRelRefs = ofRel.getVariables(false);
        unusedOfRelRefs.removeAll(ofState.getUsedReferences(false, true));
        if (unusedOfRelRefs.isEmpty()) {
            return;
        }
        Map<LLVMHeuristicVariable, LLVMHeuristicTerm> substitution =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicTerm>();
        for (LLVMHeuristicVariable ref : unusedOfRelRefs) {
            boolean notFound = true;
            for (LLVMHeuristicRelation rel : ofRelations) {
                if (rel.isEquation()) {
                    if (rel.getLhs().equals(ref)) {
                        notFound = false;
                        substitution.put(ref, rel.getRhs());
                        break;
                    } else if (rel.getRhs().equals(ref)) {
                        notFound = false;
                        substitution.put(ref, rel.getLhs());
                        break;
                    }
                }
            }
            if (notFound) {
                return;
            }
        }
        LLVMHeuristicRelation substitutedOfRel = ofRel.applySubstitution(substitution);
        if (substitutedOfRel.isEquation() && substitutedOfRel.getLhs().equals(substitutedOfRel.getLhs())) {
            // we built a tautology
            return;
        }
        LLVMHeuristicState instState = (LLVMHeuristicState)newResult.getInstState(instIsNewerState);
        LLVMHeuristicState mergeState = (LLVMHeuristicState)newResult.getGeneralizedState();
        List<Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> varMaps =
            LLVMHeuristicStateFactory.findAllRenamings(
                newResult,
                substitutedOfRel.getVariables(),
                instIsNewerState,
                false
            );
        for (Map<LLVMHeuristicVariable, LLVMHeuristicVariable> varMap : varMaps) {
            LLVMHeuristicRelation maybeInstRel = substitutedOfRel.applySubstitution(varMap);
            if (instState.getIntegerState().truthValueOfRelation(maybeInstRel, true, aborter) != YNM.YES) {
                continue;
            }
            if (LLVMHeuristicStateFactory.directedInequalityHoldsForSmallerOffset(instState, maybeInstRel, aborter)) {
                continue;
            }
            // Build image of this in the merged state, add:
            LLVMHeuristicRelation newRel =
                substitutedOfRel.applySubstitution(
                    LLVMHeuristicStateFactory.buildMergeSubstitution(newResult, varMap, instIsNewerState)
                );
            if (rels.addRelation(mergeState.getIntegerState(), newRel, false, aborter).x) {
                added.add(newRel);
            }
            return;
        }
    }

    /**
     * Hides default constructor.
     */
    protected LLVMHeuristicStateFactory() {
        // do not instantiate me from outside
    }

    @Override
    public LLVMIntersector createIntersector() {
        return new LLVMHeuristicIntersector();
    }

    @Override
    public LLVMHeuristicRelationFactory getRelationFactory() {
        return LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
    }

    @Override
    public LLVMMergeResult merge(
        LLVMAbstractState newerState,
        LLVMAbstractState olderState,
        LLVMMergeResult bestResult,
        boolean aggressive,
        boolean fastConvergence,
        Abortion aborter
    ) throws TooExpensiveException, MemoryLeakException, UndefinedBehaviorException {
        // First, check whether the two states are compatible at all.
        this.checkFormalities(newerState, olderState);
        LLVMMergeResult newResult =
            new LLVMMergeResult(bestResult, olderState, newerState, this.getRelationFactory().getTermFactory());
        //Stupipd hack: if one of the last blocks is null, the result should have null as last block as well
//        if(newerState.getLastBlock() == null || olderState.getLastBlock() == null) {
//            newResult.setGeneralizedState(newResult.getGeneralizedState().replaceLastBlock(null));
//            if(Globals.useAssertions) {
//                //Checks that we are at the first block.
//                //FIXME: This assumes that the first block of a function is always called "0" or "entry", which may break in the future.
//                //Unfortunately, we can't access the isFunctionStart() method of ProgramPosition, which does the check properly
//                //because we don't have the module here
//                assert newerState.getProgramPosition().y.equals("0") || newerState.getProgramPosition().y.equals("entry");
//            }
//        }
        // Drop all knowledge from generalized state.
        newResult.setGeneralizedState(newResult.getGeneralizedState().clearKnowledge(aborter));
        // Add general values for all variables to the result.
        LLVMHeuristicStateFactory.handleVariables(newResult, true, aggressive, fastConvergence, aborter);
        LLVMHeuristicStateFactory.handleVariables(newResult, false, aggressive, fastConvergence, aborter);
        // Add addresses known to be used from the beginning
        LLVMHeuristicStateFactory.handleInitialHeapAddresses(newResult, aggressive, fastConvergence);
        // Handle call stacks (we already know that they have the same size).
        LLVMHeuristicStateFactory.handleCallStacks(newResult, aggressive, fastConvergence);
        // Add general values for all allocated memory areas which are not covered by variables to the result.
        LLVMHeuristicStateFactory.handleAllocations(newResult, aggressive, fastConvergence);
        // Check if we need to keep variables that do not occur in the variable function but in the relations.
        LLVMHeuristicStateFactory.findReferencePairsInRelations(newResult, true, aggressive, fastConvergence, aborter);
        LLVMHeuristicStateFactory.findReferencePairsInRelations(newResult, false, aggressive, fastConvergence, aborter);
        // Handle the heap.
        LLVMHeuristicStateFactory.handlePointwiseHeap(newResult, true, aggressive, fastConvergence, aborter);
        LLVMHeuristicStateFactory.handlePointwiseHeap(newResult, false, aggressive, fastConvergence, aborter);
        LLVMHeuristicStateFactory.handleNonPointwiseHeapInvariants(newResult, true, aggressive, fastConvergence);
        LLVMHeuristicStateFactory.handleNonPointwiseHeapInvariants(newResult, false, aggressive, fastConvergence);
        LLVMHeuristicStateFactory.checkLossOfHeapInfo(newResult, true, aborter);
        LLVMHeuristicStateFactory.checkLossOfHeapInfo(newResult, false, aborter);
        LLVMHeuristicStateFactory.deduceStructHeapInvariants(newResult, true, aggressive, fastConvergence, aborter);
        LLVMHeuristicStateFactory.deduceStructHeapInvariants(newResult, false, aggressive, fastConvergence, aborter);
        // Handle associations.
        LLVMHeuristicStateFactory.handleAssociations(newResult, true);
        LLVMHeuristicStateFactory.handleAssociations(newResult, false);
        // Handle integer relations in the states.
        LLVMHeuristicStateFactory.handleRelations(newResult, true, aborter);
        LLVMHeuristicStateFactory.handleRelations(newResult, false, aborter);
        // Try to find new relations for concrete values that will not be concrete in the merged state.
        LLVMHeuristicStateFactory.guessRelations(newResult, true, aborter);
        // Add relations for array indices
        LLVMHeuristicStateFactory.handleArrayIndices(newResult, aborter);
        // Add relations for extended values.
        if(!fastConvergence) {
        	//We don't do this in fast convergence mode, because it yields too many additional relations
        	LLVMHeuristicStateFactory.handleValueExtensions(newResult, aborter);
        }
        // Add relations to keep the knowledge that several distances between variables are equal and that several
        // constants are used as array indices.
        // This should only be done after all references have been merged already.
        // entries c -> {(x, y),...} in the CommonOffsetMap represent the knowledge x = y + c
        // entries x -> {(y, c),...} in the OffsetMap also represent the knowledge x = y + c
        Pair<LLVMOffsetMap, LLVMCommonOffsetMap> newOffsets =
            LLVMHeuristicIntegerState.computeOffsetMaps(
                new LLVMHeuristicRelationSet(
                    ((LLVMHeuristicState)newResult.getNewerState()).getRelations()
                ).getEquations()
            );
        Pair<LLVMOffsetMap, LLVMCommonOffsetMap> oldOffsets =
            LLVMHeuristicIntegerState.computeOffsetMaps(
                new LLVMHeuristicRelationSet(
                    ((LLVMHeuristicState)newResult.getOlderState()).getRelations()
                ).getEquations()
            );
        LLVMHeuristicStateFactory.handleChangingCommonDistances(newResult, newOffsets, oldOffsets, aborter);
        LLVMHeuristicStateFactory.handleConstantArrayIndices(newResult, newOffsets, oldOffsets, aborter);
        this.mergeTrapValues(newResult, true);
        this.mergeTrapValues(newResult, false);
        mergeEntryStateVariableNameRecords(newResult);
        mergeAllocationChangedSinceEntryState(newResult);

        return newResult;
    }

    @Override
    protected LLVMHeuristicState emptyState(LLVMModule module, LLVMProgramPosition pos, LLVMParameters params, Abortion aborter) {
        return
            new LLVMHeuristicState(
                module,
                ImmutableCreator.create(new TreeSet<Integer>()),
                pos,
                false,
                new LLVMHeuristicIntegerState(params),
                ImmutableCreator.create(Collections.emptyMap()),
                false,
                ImmutableCreator.create(new TreeSet<Integer>()),
                null,
                null,
                params
            );
    }

    /**
     * Give triples of allocations, upper references, and offsets a name.
     * @author cryingshadow
     * @version $Id$
     */
    private static class AllocationLimitOffset extends Triple<LLVMAllocation, LLVMHeuristicVariable, BigInteger> {

        /**
         * @param allocation The allocation.
         * @param limit The upper limit.
         * @param offset The offset.
         */
        private AllocationLimitOffset(LLVMAllocation allocation, LLVMHeuristicVariable limit, BigInteger offset) {
            super(allocation, limit, offset);
        }

    }

    /**
     * Give triples of immutable pairs of references and types combined with an unsigned flag a name.
     * @author cryingshadow
     * @version $Id$
     */
    private static class DerefVarMatch
    extends Triple<
        ImmutablePair<? extends LLVMSimpleTerm, LLVMType>,
        ImmutablePair<? extends LLVMSimpleTerm, LLVMType>,
        Boolean> {

        /**
         * For serialization.
         */
        private static final long serialVersionUID = 8894591807021110517L;

        /**
         * @param key The first reference/type pair.
         * @param value The second reference/type pair.
         * @param unsigned Unsigned interpretation?
         */
        public DerefVarMatch(
            ImmutablePair<? extends LLVMSimpleTerm, LLVMType> key,
            ImmutablePair<? extends LLVMSimpleTerm, LLVMType> value,
            boolean unsigned
        ) {
            super(key, value, unsigned);
        }

    }

    /**
     * Give pairs of pairs of references a name.
     * @author cryingshadow
     * @version $Id$
     */
    private static class RefPairPair
    extends Pair<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>, Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>
    {

        /**
         * For serialization.
         */
        private static final long serialVersionUID = 4423072973869204205L;

        /**
         * @param key The first pair of references.
         * @param value The second pair of references.
         */
        public RefPairPair(
            Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> key,
            Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> value
        ) {
            super(key, value);
        }

    }

}
