package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author cotto
 */
public class InputReferences implements Iterable<InputReference>, Cloneable {

    /**
     * The root input references, indexed by their position.
     */
    private final Map<StackFramePosition, RootInputReference> rootMap;

    /**
     * The non-root input references.
     */
    private final Collection<NonRootInputReference> nonRootRefs;

    /**
     * The changed static fields.
     */
    private final Map<FieldIdentifier, IRChangeInformations> changedSF;

    /**
     * Initialize the data structures.
     */
    public InputReferences() {
        this.rootMap = new LinkedHashMap<>();
        this.nonRootRefs = new LinkedHashSet<>();
        this.changedSF = new HashMap<>();
    }

    /**
     * Fill this collection of InputReference objects with those for the specified argument. This is used when creating
     * the start state, which is not invoked explicitly.
     * @param pos a position to some argument
     * @param ref the reference stored there
     */
    public void addArgument(final LocVarRootPosition pos, final AbstractVariableReference ref) {
        this.rootMap.put(pos, new RootInputReference(ref, pos));
    }

    /**
     * The state, starting at the first opcode of some method and only consisting of a single stackframe, resulted out
     * of a method invocation in the state given as the argument. In this method we create the input references that are
     * needed to handle this specific invocation.
     * @param callingState the state that includes both the invoked method and the opcode causing the invocation.
     * @param callingGraph the MethodGraph containing the call
     */
    public void addReferencesForMethodCall(final State callingState, final MethodGraph callingGraph) {
        this.changedSF.clear();
        this.nonRootRefs.clear();
        this.rootMap.clear();

        final StackFrame topFrame = callingState.getCurrentStackFrame();
        assert (topFrame.getOperandStack().getStack().isEmpty());

        /*
         * For every reference provided to the called method (the arguments),
         * create a RootInputReference.
         */
        final Pair<Collection<RootInputReference>, Collection<AbstractVariableReference>> pair =
            InputReferences.getRootRefs(callingState);
        final Collection<RootInputReference> rootInputRefs = pair.x;

        final Collection<AbstractVariableReference> rootRefs = pair.y;
        for (final RootInputReference rootIr : rootInputRefs) {
            this.rootMap.put(rootIr.getPosition(), rootIr);
        }

        final HeapPositions heapPos = new HeapPositions(callingState, true);

        final Collection<AbstractVariableReference> changeableReferences =
            InputReferences.getChangeableReferences(callingState, heapPos, rootRefs);

        /*
         * Based on all this information, create the NRIRs we need to capture
         * all side effects (and refinements?).
         */
        this.nonRootRefs.addAll(InputReferences.cleanAndCreateNRIRs(changeableReferences, rootRefs, heapPos, callingGraph));
    }

    /**
     * @param callingState the state that includes both the invoked method and the opcode causing the invocation
     * @param reachableReferences the references that can be reached from the arguments provided to the invoked method
     * @return For a reachable reference reachRef return the references x where x -><- reachRef or x =?= reachRef
     * exists. The reachable references are removed from this set, so only "unreachable" references are returned.
     */
    private static Collection<AbstractVariableReference> getSimRefs(
        final State callingState,
        final Collection<AbstractVariableReference> reachableReferences)
    {
        final EqualityGraph eqGraph = callingState.getHeapAnnotations().getEqualityGraph();
        final JoiningStructures joins = callingState.getHeapAnnotations().getJoiningStructures();

        final Collection<AbstractVariableReference> simRefs = new LinkedHashSet<>();

        for (final AbstractVariableReference reachRef : reachableReferences) {
            simRefs.addAll(eqGraph.getPartners(reachRef));
            simRefs.addAll(joins.getReferencesWithPartner(reachRef));
        }

        simRefs.removeAll(reachableReferences);

        return simRefs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public InputReferences clone() {
        final InputReferences clone = new InputReferences();
        for (final Map.Entry<StackFramePosition, RootInputReference> entry : this.rootMap.entrySet()) {
            clone.rootMap.put(entry.getKey(), entry.getValue().clone());
        }
        for (final NonRootInputReference nonRoot : this.nonRootRefs) {
            clone.nonRootRefs.add(nonRoot.clone());
        }
        for (final Map.Entry<FieldIdentifier, IRChangeInformations> entry : this.changedSF.entrySet()) {
            clone.changedSF.put(entry.getKey(), entry.getValue().copy());
        }
        return clone;
    }

    /**
     * @param callingState the state that includes both the invoked method and the opcode causing the invocation
     * @param rootRefs the root references defining all directly reachable references
     * @return all references that can be reached using a sequence of realized fields (including the rootRefs
     * themselves). Also add references reachable from some static field.
     */
    private static Collection<AbstractVariableReference> getReachableReferences(
        final State callingState,
        final Collection<AbstractVariableReference> rootRefs)
    {

        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final AbstractVariableReference ref : rootRefs) {
            if (ref.isNULLRef()) {
                continue;
            }

            result.addAll(Reachability.getReachableRefs(ref, true, callingState));
            // ref is also reachable
            result.add(ref);
        }

        for (final AbstractVariableReference ref : callingState.getStaticFields().getValues()) {
            if (ref.isNULLRef()) {
                continue;
            }

            result.addAll(Reachability.getReachableRefs(ref, true, callingState));
            // ref is also reachable
            result.add(ref);
        }

        return result;
    }

    /**
     * @param ref the reference we are dealing with (which is also a reference in the calling state)
     * @param heapPosCallingState heap positions of the state that caused this InputReference to exist.
     * @param callingGraph the graph containing callingNode
     * @param existingNRIRs the NRIR already created for the state
     * @return a non-root input reference with the information from the arguments, this may be an already existing one
     * from callingState
     */
    private static NonRootInputReference createNRIR(
        final AbstractVariableReference ref,
        final HeapPositions heapPosCallingState,
        final MethodGraph callingGraph,
        final Collection<NonRootInputReference> existingNRIRs)
    {

        final State callingState = heapPosCallingState.getState();
        for (final NonRootInputReference nrir : existingNRIRs) {
            if (nrir.getReference().equals(ref)) {
                nrir.add(callingState, ref);
                return nrir;
            }
        }
        for (final StackFrame sf : callingState.getCallStack().getStackFrameList()) {
            for (final NonRootInputReference nrir : sf.getInputReferences().getNonRootInputReferences()) {
                if (nrir.getReference().equals(ref)) {
                    assert (callingGraph.getTerminationGraph().thisThreadHasWriteLock());
                    nrir.add(callingState, ref);
                    final NonRootInputReference clone = nrir.clone(false);
                    return clone;
                }
            }
        }
        if (Globals.DEBUG_COTTO) {
            assert (!ref.toString().startsWith("iconst"));
        }
        return new NonRootInputReference(ref, ref, heapPosCallingState);
    }

    /**
     * @param state the state containing the method call (including the new stack frame).
     * @param heapPos the heap positions for <code>state</code>
     * @param rootRefs the arguments provided to the invoked method
     * @return the references that might be touched by the method.
     */
    private static Collection<AbstractVariableReference> getChangeableReferences(
        final State state,
        final HeapPositions heapPos,
        final Collection<AbstractVariableReference> rootRefs)
    {
        /*
         * Find those references that are reachable by the called method (also regarding static fields).
         */
        final Collection<AbstractVariableReference> reachableReferences = InputReferences.getReachableReferences(state, rootRefs);

        /*
         * For the reachable references also get the \sim references.
         */
        final Collection<AbstractVariableReference> simRefs = InputReferences.getSimRefs(state, reachableReferences);

        /*
         * Remember for which references we already have an IR or will create
         * one, so that we can save some duplicated work.
         */
        final Collection<AbstractVariableReference> neededRefs = new LinkedHashSet<>();

        // add all root input references
        neededRefs.addAll(rootRefs);

        // add all \sim references
        neededRefs.addAll(simRefs);

        // also add all reachable references, cleanup later
        neededRefs.addAll(reachableReferences);

        /*
         * For the last case in AnnotationFixups we need more than immediate
         * predecessors of the reachable references.
         */
        final Collection<AbstractVariableReference> predRefs =
            InputReferences.getInterestingPredecessors(heapPos, reachableReferences, simRefs);
        neededRefs.addAll(predRefs);

        return neededRefs;
    }

    /**
     * @param changeableRefs the set of references that might be changed by a method.
     * @param rootRefs the arguments provided to the invoked method
     * @param heapPos the heap positions for <code>state</code>
     * @param callingGraph the method graph enclosing the calling state.
     * @return a set of non root input references corresponding to the minimal set of references that need to be
     * considered to correctly handle the method.
     */
    private static Collection<NonRootInputReference> cleanAndCreateNRIRs(
        final Collection<AbstractVariableReference> changeableRefs,
        final Collection<AbstractVariableReference> rootRefs,
        final HeapPositions heapPos,
        final MethodGraph callingGraph)
    {
        final State state = heapPos.getState();
        final Collection<AbstractVariableReference> remove = new LinkedHashSet<>();

        // throw out the references for which we do not need an IR
        changeableRefs.remove(AbstractVariableReference.NULLREF);
        for (final AbstractVariableReference ref : changeableRefs) {
            /*
             * For primitive values (which are no argument) we do not want to
             * create a NRIR, because it cannot be changed and the intersection
             * can still be done in the really interesting cases.
             */
            if (!ref.pointsToReferenceType()) {
                remove.add(ref);
            }

            // throw out those references that _only_ have positions in the new stack frame
            boolean onlyInside = true;
            for (final StatePosition pos : heapPos.getPositionsForRef(ref)) {
                final RootPosition rootPos = pos.getRootPosition();
                final AbstractVariableReference refAtRoot = state.getReference(rootPos);
                if (!rootRefs.contains(refAtRoot)) {
                    onlyInside = false;
                    break;
                }
            }
            if (onlyInside) {
                remove.add(ref);
            }

            // throw out those references that _only_ are reachable from a single static field
            FieldIdentifier field = null;
            boolean onlyOneField = true;
            for (final StatePosition pos : heapPos.getPositionsForRef(ref)) {
                final RootPosition rootPos = pos.getRootPosition();
                if (rootPos instanceof StaticFieldRootPosition) {
                    final StaticFieldRootPosition sfPos = (StaticFieldRootPosition) rootPos;
                    final FieldIdentifier fieldId = new FieldIdentifier(sfPos.getClassName(), sfPos.getFieldName());
                    if (field == null) {
                        field = fieldId;
                    } else if (!field.equals(fieldId)) {
                        onlyOneField = false;
                        break;
                    }
                } else {
                    onlyOneField = false;
                    break;
                }
            }
            if (onlyOneField) {
                remove.add(ref);
            }
        }
        changeableRefs.removeAll(remove);

        // we already have some IR for the root references
        changeableRefs.removeAll(rootRefs);

        final Collection<NonRootInputReference> result = new LinkedHashSet<>();
        for (final AbstractVariableReference ref : changeableRefs) {
            result.add(InputReferences.createNRIR(ref, heapPos, callingGraph, result));
        }

        return result;
    }

    /**
     * <p>
     * This method computes references that need to be represented using NRIRs because of the last case in
     * AnnotationFixups. For this case it does not suffice to have reachable references (extended using \sim).
     * </p>
     * @param heapPos the heap positions for the state containing the method call (including the new stack frame).
     * @param reachableReferences the references that are visible from the arguments (without the arguments themselves)
     * @param simRefs the \sim references for the reachable references (excluding reachable references)
     * @return the references that might get annotated in a write situation corresponding to the last case of
     * AnnotationFixups (or are needed for that annotation)
     */
    public static Collection<AbstractVariableReference> getInterestingPredecessors(
        final HeapPositions heapPos,
        final Collection<AbstractVariableReference> reachableReferences,
        final Collection<AbstractVariableReference> simRefs)
    {
        /*
         * Imagine a state with references p, parent, child, childSucc and the
         * following heap shape:
         *
         * p \rightsquigarrow parent
         * child \rightsquigarrow childSucc
         * p \rightsquigarrow childSucc
         *
         * When now writing parent.f = child, we need to add a possibly non-tree
         * annotation for p. For this we need to see that p (after the write)
         * has two paths leading to child - namely
         * 1) p to parent, then using parent.f to child, then to childSucc and
         * 2) p directly to childSucc.
         * As a consequence, we need to have a NRIR for p. For longer paths
         * to parent and childSucc starting in p, we also need to include the
         * references on these paths.
         *
         * We need to find all such references p. The first reference that needs
         * to be reached from p is the parent reference (which can be in
         * reachableRefs or simRefs). The second reference that needs to be
         * reached is childSucc, which also can be in reachableRefs or in
         * simRefs.
         *
         * We only need to consider the case where at least one of the two paths
         * has at least a single realized connection (because we already regard
         * all simPred references). Both paths may end with -><- or =?=. All
         * references on the two paths, including p itself, must be part of the
         * result, such that we have all needed information when we run
         * AnnotationFixups.
         *
         * Because the paths may end with an annotation and the reached
         * reference itself may only be reachable using an annotation, in the
         * situation p.f=x, x -><- y, reachRef -><- y we might also need to
         * consider p as a NRIR.
         *
         * 1) find concrete and abstract predecessors p of x (with all refs in
         *    between), where x is in simRefs or reachRefs
         * 2) if two such x != x' have a common predecessor p, add p and all
         *    references on the path from p to x and from p to x'
         *
         * ---------------------------------------------------------------------
         *
         * The explanation above only deals with write accesses introducing a
         * non-tree shape, but no cycle.
         *
         * p.f=...=parent, child \rightsquigarrow p, where the connection from
         * child to p ends with -><- or =?=
         *
         * We need to (additionally) include all references on the path from p
         * to parent.
         *
         * Here we may assume parent != child.
         *
         * 1) find concrete predecessors of parent (with all refs in between).
         * 2) find predecessors p with child \rightsquigarrow p (abstract!)
         * 3) for those: add p (with all refs in between)
         */

        /*
         * TODO: Maybe it is a better idea to just abstract all p candidates, so
         * that we just add these references instead of all references on the
         * path. This at least leaves no work that needs to be done for the
         * cyclic case.
         */

        // we let a lot of predecessor information
        final Map<AbstractVariableReference, CollectionMap<AbstractVariableReference, AbstractVariableReference>> preds =
            new LinkedHashMap<>();
        for (final AbstractVariableReference ref : reachableReferences) {
            InputReferences.fillPreds(heapPos, ref, preds);
        }
        for (final AbstractVariableReference ref : simRefs) {
            InputReferences.fillPreds(heapPos, ref, preds);
        }

        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();

        // non-tree: find a common predecessor p of some references x != x'
        for (final Pair<Entry<AbstractVariableReference, CollectionMap<AbstractVariableReference, AbstractVariableReference>>, Entry<AbstractVariableReference, CollectionMap<AbstractVariableReference, AbstractVariableReference>>> pair : Collection_Util
            .getPairs(preds.entrySet()))
        {
            final Collection<AbstractVariableReference> predsA = pair.x.getValue().keySet();
            final Collection<AbstractVariableReference> predsB = pair.y.getValue().keySet();
            final Collection<AbstractVariableReference> intersection = new LinkedHashSet<>(predsA);
            intersection.retainAll(predsB);
            final AbstractVariableReference x = pair.x.getKey();
            final AbstractVariableReference xPrime = pair.y.getKey();

            for (final AbstractVariableReference samePred : intersection) {
                /*
                 * We may (and should!) ignore samePred if every path from
                 * samePred to x also leads through x' (or vice versa). Example:
                 * oP.f = o1, o1.f = o2. o1 and o2 are in reachRefs, but oP
                 * should not be seen as a interesting predecessor.
                 */
                if (InputReferences.alwaysOnPath(x, xPrime, heapPos) || InputReferences.alwaysOnPath(xPrime, x, heapPos)) {
                    continue;
                }

                // add everything from samePred to x and from samePred to xPrime
                result.addAll(pair.x.getValue().get(samePred));
                result.addAll(pair.y.getValue().get(samePred));
                assert (pair.x.getValue().get(samePred).contains(samePred));
                assert (pair.y.getValue().get(samePred).contains(samePred));
                assert (pair.x.getValue().get(samePred).contains(x));
                assert (pair.y.getValue().get(samePred).contains(xPrime));
            }
        }

        final State state = heapPos.getState();

        // cyclic
        /*
         * First find a predecessor p of parent with child \rightsquigarrow p
         * (where the path from child to p must end with an abstract
         * connection).
         */
        final Collection<AbstractVariableReference> parentCandidates = new LinkedHashSet<>();
        parentCandidates.addAll(reachableReferences);
        parentCandidates.addAll(simRefs);
        for (final AbstractVariableReference parent : parentCandidates) {
            if (!parent.pointsToReferenceType()) {
                continue;
            }
            if (parent.isNULLRef()) {
                continue;
            }
            final CollectionMap<AbstractVariableReference, AbstractVariableReference> parentPreds = preds.get(parent);
            for (final Entry<AbstractVariableReference, Collection<AbstractVariableReference>> entry : parentPreds
                .entrySet())
            {
                final AbstractVariableReference p = entry.getKey();
                /*
                 * Is there a path from some child reference to p which ends
                 * with an abstract part?
                 */
                final Collection<AbstractVariableReference> pSimPreds = new LinkedHashSet<>();
                pSimPreds.addAll(state.getHeapAnnotations().getEqualityGraph().getPartners(p));
                pSimPreds.addAll(state.getHeapAnnotations().getJoiningStructures().getReferencesWithPartner(p));
                for (final AbstractVariableReference pSimPred : pSimPreds) {
                    InputReferences.fillPreds(heapPos, pSimPred, preds);
                    for (final Map.Entry<AbstractVariableReference, Collection<AbstractVariableReference>> innerEntry : preds
                        .get(pSimPred)
                        .entrySet())
                    {
                        final AbstractVariableReference child = innerEntry.getKey();
                        if (!reachableReferences.contains(child) && !simRefs.contains(child)) {
                            continue;
                        }
                        /*
                         * We have p.f=...=parent and child \rightsquigarrow p,
                         * where the path from child to p ends with an abstract
                         * connection. When writing parent.f=child we need to
                         * see everything on the path from p to parent in order
                         * to correctly add cyclic annotations.
                         */
                        result.addAll(entry.getValue());
                    }
                }
            }
        }

        return result;
    }

    /**
     * @param first a reference
     * @param second another reference
     * @param heapPos heapPositions of the state to analyze
     * @return true if every path to second also goes through first
     */
    private static boolean alwaysOnPath(
        final AbstractVariableReference first,
        final AbstractVariableReference second,
        final HeapPositions heapPos)
    {
        for (final StatePosition pos : heapPos.getPositionsForRef(second)) {
            final LinkedHashSet<AbstractVariableReference> refs = new LinkedHashSet<>();
            pos.getReferencesOnPath(heapPos.getState(), refs);
            if (!refs.contains(first)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Fill preds with predecessor information for ref. This method adds a map for ref, where the key of this map is
     * some predecessor pred. The associated value is a set of references which are on the path from pred to ref.
     * @param heapPos the heap positions of the state to work on
     * @param ref the reference for which we need the predecessors
     * @param preds fill in information here
     */
    private static void fillPreds(
        final HeapPositions heapPos,
        final AbstractVariableReference ref,
        final Map<AbstractVariableReference, CollectionMap<AbstractVariableReference, AbstractVariableReference>> preds)
    {
        if (preds.containsKey(ref)) {
            return;
        }
        if (!ref.pointsToReferenceType()) {
            return;
        }
        if (ref.isNULLRef()) {
            return;
        }

        final State state = heapPos.getState();

        final CollectionMap<AbstractVariableReference, AbstractVariableReference> inBetween = new CollectionMap<>();
        final CollectionMap<AbstractVariableReference, NonRootPosition> predecessors =
            AnnotationFixups.getAllPredecessors(ref, heapPos);
        for (final Map.Entry<AbstractVariableReference, Collection<NonRootPosition>> entry : predecessors.entrySet()) {
            final AbstractVariableReference pred = entry.getKey();
            final StatePosition predPos = heapPos.getShortestPositionForRef(pred);
            // all NRPs lead from pred to ref, collect the references in between
            for (final NonRootPosition nrp : entry.getValue()) {
                inBetween.add(pred, pred);
                if (nrp == null) {
                    continue;
                }
                for (final StatePosition pos : nrp.getPathToRoot()) {
                    assert (pos instanceof NonRootPosition);
                    final AbstractVariableReference betweenRef =
                        state.getReference(predPos.append((NonRootPosition) pos));
                    inBetween.add(pred, betweenRef);
                }
            }
        }
        preds.put(ref, inBetween);
    }

    /**
     * @param res add the known references here
     */
    public void getReferences(final Map<AbstractVariableReference, Integer> res) {
        for (final InputReference iRef : this) {
            final AbstractVariableReference ref = iRef.getReference();
            res.put(ref, Integer.valueOf(res.get(ref).intValue() + 1));
        }
    }

    /**
     * @return list of input references in this state (order is stable!)
     */
    public List<AbstractVariableReference> getReferences() {
        final List<AbstractVariableReference> res = new LinkedList<>();
        for (final InputReference iRef : this) {
            final AbstractVariableReference ref = iRef.getReference();
            res.add(ref);
        }
        return res;
    }

    /**
     * @param callingState the state with a fresh stackframe for the invoked method on top
     * @return For each argument of the invoked method, the reference is returned. These references define all
     * the references that are directly visible from the invoked method. The RIRs are created such that they point to
     * the reference in the calling state (i.e., most likely on the operand stack), because these positions still exist
     * when the called method returns. If the argument is not visible from the call site, no corresponding IR is
     * created.
     */
    private static Pair<Collection<RootInputReference>, Collection<AbstractVariableReference>> getRootRefs(
        final State callingState)
    {
        final Collection<RootInputReference> rootInputRefs = new LinkedHashSet<>();
        final Collection<AbstractVariableReference> allRefs = new LinkedHashSet<>();

        final StackFrame callingFrame = callingState.getCallStack().get(1);
        final OpCode callingOpCode = callingFrame.getCurrentOpCode();

        // be careful with freshly thrown exceptions
        if (callingFrame.hasException()) {
            rootInputRefs.add(new RootInputReference(callingFrame.getException(), LocVarRootPosition.create(0, 0)));
        } else {
            int numArgs;
            assert (callingOpCode instanceof InvokeMethod);
            final InvokeMethod invokeOpcode = (InvokeMethod) callingOpCode;
            numArgs = invokeOpcode.getMethodIdentifier().getDescriptor().getArgumentCount();
            if (!callingState.getCurrentOpCode().getMethod().isStatic()) {
                // this
                numArgs++;
            }

            final LocalVariables locVars = callingState.getCurrentStackFrame().getLocalVariables();

            final IMethod method = callingState.getCurrentStackFrame().getMethod();
            final Collection<Integer> activeList = method.getActiveVariables(callingState.getCurrentOpCode().getPos());

            final State clone = callingState.clone();
            clone.getCallStack().pop();
            final Set<AbstractVariableReference> callReferences = clone.getReferences().keySet();

            for (int i = numArgs - 1; i >= 0; i--) {
                final int locVarIndex = numArgs - i - 1;
                if (!activeList.contains(Integer.valueOf(locVarIndex))) {
                    continue;
                }
                final AbstractVariableReference ref = locVars.getLocalVariable(locVarIndex);

                allRefs.add(ref);

                /*
                 * Is the reference still in use in the calling state? Throwing out references might save a lot of work
                 * with annotations.
                 *
                 * CAppE:              We need to know that we invoked appE with a positive number, given by an interval
                 *                     [1, +infty). There is no other need to create a RootIR for this argument.
                 * SharingAnalysisRec: We need to know that we invoked appendNewList with the constant 1 in the first
                 *                     call.
                 */
                if (!callReferences.contains(ref) && !ref.isNULLRef() && ref.pointsToReferenceType()) {
                    continue;
                }

                final StackFramePosition pos = LocVarRootPosition.create(0, locVarIndex);
                rootInputRefs.add(new RootInputReference(ref, pos));
            }
        }

        return new Pair<>(rootInputRefs, allRefs);
    }

    public void markInstanceFieldAsChanged(HeapPositions heapPos, AbstractVariableReference objectRef,
            FieldIdentifier field, AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        IrChangeInformation changeInformation =
                IrChangeInformation.create(heapPos, objectRef, newValue, oldValue);
        this.markAsChanged(heapPos, objectRef, changeInformation, field);
    }

    public void markArrayAsChanged(HeapPositions heapPos, AbstractVariableReference arrayRef,
            AbstractVariableReference indexRef,
            AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        IrChangeInformation changeInformation =
                IrChangeInformation.create(heapPos, arrayRef, newValue, oldValue);
        this.markAsChanged(heapPos, arrayRef, changeInformation, null);
    }

    private void markAsChanged(HeapPositions heapPos, AbstractVariableReference ref, IrChangeInformation change,
            FieldIdentifier field) {
        assert (!ref.isNULLRef());
        // it is not possible to change an integer
        assert (ref.pointsToReferenceType());
        Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> changedRefsAndPreds = computeChangedRefs(ref, heapPos);
        putChange(changedRefsAndPreds.x, change, field);
        propagateChange(changedRefsAndPreds.y, Collections.singleton(change));
        propagateToStaticFields(heapPos.getState(), changedRefsAndPreds.x, changedRefsAndPreds.y, Collections.singleton(change));
    }

    /**
     * Add all changes describe in changes to this state
     * @param heapPos position of the changes
     * @param ref changed references
     * @param changes changes on that reference
     */
    public void addChanges(HeapPositions heapPos, AbstractVariableReference ref, IRChangeInformations changes) {
        assert (!ref.isNULLRef());
        // it is not possible to change an integer
        assert (ref.pointsToReferenceType());
        Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> changedRefsAndPreds = computeChangedRefs(ref, heapPos);
        putChanges(changedRefsAndPreds.x, changes);
        Collection<IrChangeInformation> summarisedChanges = changes.summariseAllChanges().values();
        propagateChange(changedRefsAndPreds.y, summarisedChanges);
        propagateToStaticFields(heapPos.getState(), changedRefsAndPreds.x, changedRefsAndPreds.y, summarisedChanges);
    }

    private Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> computeChangedRefs(AbstractVariableReference ref, HeapPositions heapPos) {
        State state = heapPos.getState();
        Set<AbstractVariableReference> changedRefs = new LinkedHashSet<>();
        changedRefs.add(ref);
        changedRefs.addAll(state.getHeapAnnotations().getEqualityGraph().getPartners(ref));

        Set<AbstractVariableReference> changedRefPreds = new LinkedHashSet<>(changedRefs);
        changedRefPreds.addAll(state.getHeapAnnotations().getJoiningStructures().getReferencesWithPartner(ref));
        changedRefPreds = changedRefPreds.stream()
            .flatMap(r -> heapPos.getAllPredecessors(r, true).stream())
            .collect(Collectors.toSet());
        changedRefPreds.removeAll(changedRefs);
        return new Pair<>(changedRefs, changedRefPreds);
    }

    private Set<InputReference> putChange(Set<AbstractVariableReference> changedRefs, IrChangeInformation change,
            FieldIdentifier field) {
        Set<InputReference> changedIrs = new HashSet<>();
        for (InputReference ir : this) {
            if (changedRefs.contains(ir.getReference())) {
                changedIrs.add(ir);
                ir.putLocalChange(change, field);
            }
        }
        return changedIrs;
    }

    private Set<InputReference> putChanges(Set<AbstractVariableReference> changedRefs, IRChangeInformations changes) {
        Set<InputReference> changedIrs = new HashSet<>();
        for (InputReference ir : this) {
            if (changedRefs.contains(ir.getReference())) {
                changedIrs.add(ir);
                ir.mergeChanges(changes);
            }
        }
        return changedIrs;
    }

    private void propagateChange(Set<AbstractVariableReference> changedRefPreds, Collection<IrChangeInformation> changes) {
        for (InputReference ir : this) {
            if (changedRefPreds.contains(ir.getReference())) {
                for (IrChangeInformation change : changes) {
                    ir.addReachableChange(change);
                }
            }
        }
    }

    private void propagateToStaticFields(State state, Set<AbstractVariableReference> changedRefs, Set<AbstractVariableReference> changedRefPreds, Collection<IrChangeInformation> changes) {
        for (Entry<ClassName, Map<String, AbstractVariableReference>> outerEntry : state.getStaticFields().getEntries()) {
            for (Entry<String, AbstractVariableReference> innerEntry : outerEntry.getValue().entrySet()) {
                if (changedRefs.contains(innerEntry.getValue()) ||
                        changedRefPreds.contains(innerEntry.getValue())) {
                    IRChangeInformations sFChanges =
                            changedSF.computeIfAbsent(new FieldIdentifier(outerEntry.getKey(),  innerEntry.getKey()), k -> new IRChangeInformations());
                    for (IrChangeInformation change : changes) {
                        sFChanges.addReachableChange(change, null);
                    }
                }
            }
        }
    }

    public void markStaticFieldAsChanged(HeapPositions heapPos, FieldIdentifier field,
            AbstractVariableReference newValue, AbstractVariableReference oldValue) {
        IrChangeInformation changeInformation =
                IrChangeInformation.create(heapPos, field, newValue, oldValue);
        IRChangeInformations changes = this.changedSF.computeIfAbsent(field, k -> new IRChangeInformations());
        changes.clear();
        changes.addLocalChange(changeInformation, null);
    }

    /**
     * Rename a reference for each corresponding InputReference
     * @param oldRef the old name
     * @param newRef the new name
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        for (final InputReference inputRef : this) {
            inputRef.replaceReference(oldRef, newRef);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb, null, null, true);
        return sb.toString();
    }

    /**
     * Fill the StringBuilder with a nice string representation.
     * @param sb a StringBuilder
     * @param varUsers a map giving information about the number of places the given reference is used.
     * @param shortRepresentation if some value only occurs at a single position, show the value instead of the
     * reference
     * @param state the state containing these input references
     */
    public void toString(
        final StringBuilder sb,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        final Iterator<InputReference> it = this.iterator();
        if (!this.changedSF.isEmpty()) {
            sb.append(this.changedSF.toString());
        }
        if (!it.hasNext()) {
            return;
        }
        sb.append('[');
        while (it.hasNext()) {
            final InputReference inputReference = it.next();
            inputReference.toString(sb, varUsers, state, shortRepresentation);
            if (it.hasNext()) {
                sb.append(", ");
                /*
                if (inputReference instanceof NonRootInputReference) {
                    sb.append("\n");
                }
                */
            }
        }
        sb.append(']');
        sb.append("\n");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Iterator<InputReference> iterator() {
        return new Iterator<InputReference>() {
            private final Iterator<RootInputReference> rootIt = InputReferences.this.rootMap.values().iterator();
            private final Iterator<NonRootInputReference> nonRootIt = InputReferences.this.nonRootRefs.iterator();

            /**
             * {@inheritDoc}
             */
            @Override
            public boolean hasNext() {
                if (this.rootIt.hasNext()) {
                    return true;
                }
                return this.nonRootIt.hasNext();
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public InputReference next() {
                if (this.rootIt.hasNext()) {
                    return this.rootIt.next();
                }
                return this.nonRootIt.next();
            }

            /**
             * {@inheritDoc}
             */
            @Override
            public void remove() {
                assert (false);
            }
        };
    }

    public Iterable<IRChangeInformations> getChangeInformations() {
        return new Iterable<IRChangeInformations>() {
            @Override
            public Iterator<IRChangeInformations> iterator() {
                return new Iterator<IRChangeInformations>() {
                    Iterator<IRChangeInformations> sfs = changedSF.values().iterator();
                    Iterator<InputReference> irs = InputReferences.this.iterator();
                    InputReference next;
                    {advanceIrs();}

                    @Override
                    public boolean hasNext() {
                        return sfs.hasNext() || next != null;
                    }

                    @Override
                    public IRChangeInformations next() {
                        if (sfs.hasNext())
                            return sfs.next();
                        if (next == null) {
                            throw new NoSuchElementException();
                        }
                        InputReference res = next;
                        advanceIrs();
                        return res.getChanges();
                    }

                    void advanceIrs() {
                        while (irs.hasNext()) {
                            next = irs.next();
                            if (next.getChanged()) {
                                return;
                            }
                        }
                        next = null;
                    }
                };
            }
        };
    }

    /**
     * Add the given input reference.
     * @param ir the input reference to add.
     */
    public void add(final InputReference ir) {
        if (ir instanceof RootInputReference) {
            this.add((RootInputReference) ir);
        } else {
            assert (ir instanceof NonRootInputReference);
            this.add((NonRootInputReference) ir);
        }
    }

    /**
     * Add the given root input reference.
     * @param ir the root input reference to add.
     */
    public void add(final RootInputReference ir) {
        this.rootMap.put(ir.getPosition(), ir);
    }

    /**
     * Add the given non-root input reference.
     * @param ir the non-root input reference to add.
     */
    public void add(final NonRootInputReference ir) {
        this.nonRootRefs.add(ir);
    }

    /**
     * @return the known root input references
     */
    public Collection<RootInputReference> getRootInputReferences() {
        return this.rootMap.values();
    }

    /**
     * @param position a position in the state
     * @return the root input reference for the given position
     */
    public RootInputReference getRootInputReference(final StatePosition position) {
        return this.rootMap.get(position);
    }

    /**
     * @return all known non-root input references
     */
    public Collection<NonRootInputReference> getNonRootInputReferences() {
        return this.nonRootRefs;
    }

    /**
     * Reverse a static field change
     * @param className the name of the class containing the field
     * @param fieldName the name of the field
     * @return true iff the entry was added
     */
    public void setUnchanged(final FieldIdentifier staticField) {
        this.changedSF.remove(staticField);
    }

    /**
     * @param className the name of the class containing the field
     * @param name the name of the field
     * @return true if we remembered a write access to the specified static field.
     */
    public boolean wasChanged(final FieldIdentifier staticField) {
        return this.changedSF.containsKey(staticField);
    }

    public Optional<IRChangeInformations> getChangeInformation(FieldIdentifier staticField) {
        return Optional.ofNullable(this.changedSF.get(staticField));
    }

    /**
     * @return the changed static fields
     */
    public Map<FieldIdentifier, IRChangeInformations> getChangedSF() {
        return this.changedSF;
    }

    /**
     * @param ir some non-root input reference
     * @return the input reference that shares the same set of state-reference pairs (or null if it does not exist).
     */
    public NonRootInputReference getNonRootInputReference(final NonRootInputReference ir) {
        for (final NonRootInputReference nrIr : this.nonRootRefs) {
            if (nrIr.sameOrigin(ir)) {
                return nrIr;
            }
        }
        return null;
    }

    /**
     * @param ir some input reference
     * @return the input reference corresponding to the given input reference
     */
    public InputReference getInputReference(final InputReference ir) {
        if (ir instanceof RootInputReference) {
            return this.getRootInputReference(((RootInputReference) ir).getPosition());
        }
        assert (ir instanceof NonRootInputReference);
        return this.getNonRootInputReference((NonRootInputReference) ir);
    }

    /**
     * @param frameNum the frame number containing this IRs (most of the times this is 0).
     * @return the root positions defined by the input references
     */
    public Collection<InputRefRootPosition> getIRPositions(final int frameNum) {
        final Collection<InputRefRootPosition> result = new LinkedHashSet<>();
        for (final StackFramePosition pos : this.rootMap.keySet()) {
            result.add(RootIRPosition.create(pos, frameNum));
        }
        for (final NonRootInputReference nrir : this.nonRootRefs) {
            result.add(nrir.getIRStatePosition(frameNum));
        }
        return result;
    }

    /**
     * For all NRIRs remove references to states that do not exist anymore.
     * @param states all existing states
     */
    public void clean(final Collection<State> states) {
        for (final NonRootInputReference ir : this.nonRootRefs) {
            ir.clean(states);
        }
    }

    /**
     * Remove the NRIR referencing the same origin as the given NRIR.
     * @param removeMe a NRIR
     * @return true iff the corresponding reference was removed
     */
    public boolean removeNRIR(final NonRootInputReference removeMe) {
        final NonRootInputReference contained = this.getNonRootInputReference(removeMe);
        if (contained != null) {
            return this.nonRootRefs.remove(contained);
        }
        return false;
    }

    /**
     * @param ref some reference
     * @return true iff there is some NRIR named with the given reference
     */
    public boolean isNRIR(final AbstractVariableReference ref) {
        for (final NonRootInputReference nrir : this.nonRootRefs) {
            if (nrir.getReference().equals(ref)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return the references of all NRIRs
     */
    public Collection<AbstractVariableReference> getNRIRs() {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final NonRootInputReference nrir : this.nonRootRefs) {
            result.add(nrir.getReference());
        }
        return result;
    }

    /**
     * Clear everything.
     */
    public void clear() {
        this.changedSF.clear();
        this.nonRootRefs.clear();
        this.rootMap.clear();
    }

    /**
     * @param inputRef an input reference
     * @return the corresponding input reference for the given one (same position for root IRs, same set of origins for
     * NRIRs)
     */
    public InputReference getCorrespondingIR(final InputReference inputRef) {
        if (inputRef instanceof NonRootInputReference) {
            return this.getNonRootInputReference((NonRootInputReference) inputRef);
        } else {
            assert (inputRef instanceof RootInputReference);
            return this.rootMap.get(((RootInputReference) inputRef).getPosition());
        }
    }
}
