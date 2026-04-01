package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.CallExpander.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Utility class holding methods useful for generating and checking witnesses.
 *
 * @author Marc Brockschmidt
 */
public final class WitnessUtilities {
    /**
     * Constructor that you should not use.
     */
    private WitnessUtilities() {
        assert false : "Thou shall not instantiate me!";
    }

    private static class Todo {
        MethodGraph graph;
        State witness;
        Node abstrNode;
        int steps;
        boolean applyRefAssignment;
    }

    /**
     * @param methodGraph the enclosing method graph
     * @param graphNode some graph node
     * @param interestingInstance some instance of <code>graphNode</code>
     * @param refAssignment an assignment of abstract variable references to literal integer values.
     * @param aborter an aborter
     * @return instances of the method start state that we suspect is evaluated to an instance of
     * <code>interestingInstance</code>. If no such state can be constructed, we return an empty collection.
     * @throws AbortionException if we were aborted.
     */
    public static Collection<State> findStartStateWitnessesForState(final MethodGraph methodGraph,
        final Node graphNode,
        final State interestingInstance,
        final Map<AbstractVariableReference, Long> refAssignment,
        boolean onlyUpdateTopFrame,
        final Abortion aborter) throws AbortionException {
        final Collection<State> result = new LinkedHashSet<>();

        IMethod startMethod = interestingInstance.getTerminationGraph().getStartGraph().getParsedMethod();
        final Collection<State> seenEmptyIntersectionStates = new LinkedHashSet<>();
        final Todo todo = new Todo();
        todo.graph = methodGraph;
        todo.witness = interestingInstance;
        todo.abstrNode = graphNode;
        todo.steps = 0;
        todo.applyRefAssignment = true;
        final LinkedList<Todo> todoList = new LinkedList<>();
        todoList.offer(todo);
        while (!todoList.isEmpty()) {
            final Todo cur = todoList.poll();

            aborter.checkAbortion();

            final MethodGraph curGraph = cur.graph;
            State curWitness;
            if (cur.applyRefAssignment) {
                curWitness = SMTUtilities.applyRefAssignmentToState(cur.witness, refAssignment, onlyUpdateTopFrame);
            } else {
                curWitness = cur.witness;
            }
            final Node curAbstrNode = cur.abstrNode;
            final int steps = cur.steps;
            final int newSteps = Integer.valueOf(steps + 1);
            if (steps > JBCOptions.MAXIMAL_WITNESS_VERIFICATION_STEPS / 3) {
                break;
            }
            try {
                final State curAbstrState = curAbstrNode.getState();

                //Check if our abstract state represents our current witness:
                if (Globals.useAssertions) {
                    // disregard defreach-info
                    final State clone = curAbstrState.clone();
                    clone.getHeapAnnotations().getDefiniteReachabilities().clear();
                    clone.getHeapAnnotations().getArrayInfo().clear();
                    clone.getIntegerRelations().clear();
                    assert (new PathMerger().isInstance(curWitness, clone)) : "Witness does not correspond to graph node!";
                }
                final Map<AbstractVariableReference, AbstractVariableReference> abstrRefToConcrRefMap =
                    WitnessUtilities.computeReferenceMapping(curAbstrState, curWitness);

                /*
                 * Check all incoming edges of the corresponding graph node and
                 * try to find one predecessor that is useful for witness
                 * generation. In case of evaluations, we should have only
                 * predecessor and we can apply reverse evaluation.
                 * In case of refinements, we can just re-use our state, as it
                 * is more refined than the predecessor.
                 * In case of instances, we have to choose the "right" predecessor
                 * by heuristics.
                 */
                final Set<Edge> inEdges = curAbstrNode.getInEdges();

                if (startMethod.equals(curWitness.getCallStack().getTop().getMethod())
                    && (inEdges.size() == 0 || (curWitness.getCallStack().size() == 1 && curWitness.getCurrentOpCode().getPos() == 0))) {
                    // We are done for this path:
                    result.add(curWitness);
                } else if (curGraph.getStartNode().equals(curAbstrNode)) {
                    //We have reached the start of the current Method graph. Time to switch to one nearer to the start.
                    for (final MethodEndListener listener : curGraph.getMethodEndListeners()) {
                        //Do not go back to the same graph:
                        if (listener.getMethodGraph().equals(curGraph)) {
                            continue;
                        }

                        //Find the abstracted call node, try continuing there:
                        Node abstractedCallNode = null;
                        for (final Edge outEdge : listener.getNode().getOutEdges()) {
                            if (outEdge.getLabel() instanceof CallAbstractEdge) {
                                abstractedCallNode = outEdge.getEnd();
                            }
                        }

                        if (abstractedCallNode != null) {
                            //For the witness, try to compute the intersection with the call site:
                            final State abstractedCallState = abstractedCallNode.getState();
                            try {
                                final State newWitness = Intersector.intersect(curWitness, abstractedCallState);

                                Todo newTodo = new Todo();
                                newTodo.graph = listener.getMethodGraph();
                                newTodo.witness = newWitness;
                                newTodo.abstrNode = abstractedCallNode;
                                newTodo.steps = newSteps;
                                // if we are allowed to update all frames, than we can also update frames after reversing a method call
                                newTodo.applyRefAssignment = !onlyUpdateTopFrame;
                                todoList.add(newTodo);
                            } catch (final IntersectionFailException e) {
                                //Ignore the shit out of this
                            }
                        }
                    }
                } else if (inEdges.size() == 1) {
                    // If we have one predecessor, there is not much guesswork involved:
                    final Edge incomingEdge = inEdges.iterator().next();

                    final State predecessorState = incomingEdge.getStart().getState();
                    //Don't do the class init dance at the beginning:
                    final ClassName classOfStartedMethod =
                        predecessorState.getCallStack().get(predecessorState.getCallStack().size() - 1).getMethod().getClassName();
                    if (predecessorState.getClassInitInfo().getClassesWithInitializationState(interestingInstance.getJBCOptions()).get(
                        classOfStartedMethod) == InitStatus.RUNNING) {
                        result.add(curWitness);
                    }

                    final State newWitness =
                        WitnessUtilities.traverseEdgeBackwards(curWitness, incomingEdge, abstrRefToConcrRefMap, refAssignment);
                    //Traversing the edge failed, give up for this path:
                    if (newWitness != null) {
                        final Node newAbstrNode = incomingEdge.getStart();

                        Todo newTodo = new Todo();
                        newTodo.graph = curGraph;
                        newTodo.witness = newWitness;
                        newTodo.abstrNode = newAbstrNode;
                        newTodo.steps = newSteps;
                        newTodo.applyRefAssignment = cur.applyRefAssignment;
                        todoList.add(newTodo);
                    }
                } else {
                    //Guessing required.
                    int instancePredecessors = 0;
                    Edge nonInstEdge = null;
                    for (final Edge e : inEdges) {
                        if (e.getLabel() instanceof InstanceEdge) {
                            instancePredecessors++;
                        } else {
                            nonInstEdge = e;
                        }
                    }
                    assert (inEdges.size() - instancePredecessors <= 1) : "Node has more than one non-instance predecessor!";

                    //We have a proper predecessor: Use it.
                    if (nonInstEdge != null) {
                        final State newWitness =
                            WitnessUtilities.traverseEdgeBackwards(curWitness, nonInstEdge, abstrRefToConcrRefMap, refAssignment);
                        //Traversing the edge failed, give up:
                        if (newWitness != null) {
                            final Node newAbstrNode = nonInstEdge.getStart();

                            Todo newTodo = new Todo();
                            newTodo.graph = curGraph;
                            newTodo.witness = newWitness;
                            newTodo.abstrNode = newAbstrNode;
                            newTodo.steps = newSteps;
                            newTodo.applyRefAssignment = cur.applyRefAssignment;
                            todoList.add(newTodo);
                        }
                    } else {
                        /*
                         * See if there is a predecessor with a non-empty intersection. If so, just continue along the
                         * path with the intersected information (which may result in very many steps of
                         * backwards-evaluation). If there is a state resulting in an empty intersection, we
                         * additionally just guess values that hopefully lead to the current witness.
                         *
                         *  As an example consider
                         *  for (int i = 0; i < 10001; i++) {
                         *      if (i == 10000) {
                         *         for (int j = 0; j <= 0; j += 0) {
                         *         }
                         *      }
                         *  }
                         *
                         *  A witness for the inner non-terminating loop knows i == 10000. The graph contains an
                         *  instance edge ("is instance") from the computation i = 9999 to i = 10000. By intersecting
                         *  the information we can traverse this loop backwards and, after many steps, reach i = 0 and
                         *  are done.
                         *
                         *  However, there also is an instance edge (caused by a merge) from a state with i = [0, 3] to
                         *  a state with i = [i, 10000) (or maybe +infty, does not matter). When intersecting the
                         *  witness information i = 10000 with i = [0, 3] we get an empty intersection. Here we just
                         *  guess that a value of i in [0, 3] leads to i = 10000 eventually (this is checked by forward
                         *  evaluation later). This is just an approximation, but fewer steps are needed to reach the
                         *  method start state.
                         */
                        boolean foundIntersection = false;
                        for (final Edge edge : inEdges) {
                            final Node inNode = edge.getStart();
                            final State inState = inNode.getState();
                            State intersectedState = null;
                            try {
                                intersectedState = Intersector.intersect(inState, curWitness);
                            } catch (final IntersectionFailException e) {
                                //ignore;
                            }
                            if (intersectedState == null) {
                                /*
                                 * Going backwards through inState is not a good idea, because the information does not
                                 * match. However, if this is a proper merge, we may just be lucky and can guess values
                                 * that lead to the current witness when doing a proper forward evaluation.
                                 */
                                final EdgeInformation label = edge.getLabel();
                                assert (label instanceof InstanceEdge);
                                if (((InstanceEdge) label).isFromMerge()) {
                                    // we just use inState, maybe this is good enough
                                    final State newWitness = inState;

                                    // only do this once for each state
                                    if (seenEmptyIntersectionStates.add(newWitness)) {
                                        final Node newAbstrNode = inNode;
                                        Todo newTodo = new Todo();
                                        newTodo.graph = curGraph;
                                        newTodo.witness = newWitness;
                                        newTodo.abstrNode = newAbstrNode;
                                        newTodo.steps = newSteps;
                                        newTodo.applyRefAssignment = cur.applyRefAssignment;
                                        todoList.add(newTodo);
                                    }
                                }
                                continue;
                            } else {
                                /*
                                 * Intersection was successful. We only want to go through one such instance edge,
                                 * though.
                                 */
                                if (!foundIntersection) {
                                    foundIntersection = true;
                                    final State newWitness = intersectedState;
                                    final Node newAbstrNode = inNode;
                                    Todo newTodo = new Todo();
                                    newTodo.graph = curGraph;
                                    newTodo.witness = newWitness;
                                    newTodo.abstrNode = newAbstrNode;
                                    newTodo.steps = newSteps;
                                    newTodo.applyRefAssignment = cur.applyRefAssignment;
                                    todoList.add(newTodo);
                                }
                            }
                        }
                    }
                }
            } catch (final Throwable e) {
                //Something failed, don't whine:
                if (Globals.DEBUG_MARC || Globals.DEBUG_THIES) {
                    e.printStackTrace();
                }
            }
        }

        result.forEach(state -> state.getCallStack().getFromBottom(1).getInputReferences().clear()); //clean IRs
        result.removeIf(WitnessUtilities::canIgnoreInvariants);
        return result;
    }

    /**
     * Handle backwards traversal of a single edge
     * @param curWitness the current proto-witness for nontermination.
     * @param e Some edge, where <code>e.getEnd()</code> contains a state
     *  that represents <code>curWitness</code>
     * @param abstrRefToConcrRefMap Mapping between references in
     *  <code>e.getEnd()</code> and <code>curWitness</code>.
     * @param refAssignment an assignment of abstract variable references to
     *  literal integer values.
     * @return new witness at an earlier program position and the corresponding
     *  state from the termination graph.
     */
    public static State traverseEdgeBackwards(final State curWitness,
        final Edge e,
        final Map<AbstractVariableReference, AbstractVariableReference> abstrRefToConcrRefMap,
        final Map<AbstractVariableReference, Long> refAssignment) {
        final EdgeInformation edgeLabel = e.getLabel();
        final Node predecessorNode = e.getStart();
        final State predecessorState = predecessorNode.getState();

        State newWitness;
        if (edgeLabel instanceof EvaluationEdge) {
            for (final AbstractVariableReference ref : predecessorState.getReferences().keySet()) {
                if (ref.pointsToAnyIntegerType() && refAssignment.containsKey(ref)) {
                    final Long val = refAssignment.get(ref);
                    final AbstractVariable origVar = predecessorState.getAbstractVariable(ref);
                    assert (origVar instanceof AbstractInt) : "Trying to set non-int reference to integer value";
                    final LiteralInt newVar = AbstractInt.create(val);
                    final AbstractVariableReference newRef =
                        curWitness.createReferenceAndAdd(newVar, ref.getPrimitiveType());
                    abstrRefToConcrRefMap.put(ref, newRef);
                    curWitness.replaceReference(ref, newRef);
                }
            }
            final State successorState = e.getEnd().getState();
            // did we deal with a thrown exception?
            if (predecessorState.getCurrentStackFrame().hasException()
                && successorState.getCallStack().size() == predecessorState.getCallStack().size()) {
                /*
                 * We need to set the exception bit and change the program position.
                 */
                newWitness = successorState.clone();
                final AbstractVariableReference exceptionRef =
                    newWitness.getCurrentStackFrame().getOperandStack().pop();
                newWitness.getCurrentStackFrame().setException(exceptionRef);
                newWitness.getCurrentStackFrame().setCurrentOpCode(predecessorState.getCurrentOpCode());
            } else {
                newWitness =
                    predecessorState.getCurrentOpCode().reverseEvaluation(predecessorState, successorState, curWitness,
                        abstrRefToConcrRefMap);
            }
            predecessorState.getCurrentOpCode().handleActiveVarChangesInRevEv(predecessorState, successorState,
                newWitness, abstrRefToConcrRefMap);
        } else if (edgeLabel instanceof RefinementEdge || edgeLabel instanceof SplitEdge) {
            //Do nothing. Yay!
            newWitness = curWitness;
        } else if (edgeLabel instanceof InstanceEdge) {
            //Try to use possibly more concrete information:
            try {
                newWitness = Intersector.intersect(predecessorState, curWitness);
            } catch (final IntersectionFailException failExc) {
                /*
                 * This might happen if we had some var: [0, 2] which was
                 * widened in the merging process to [0, inf). If in our current
                 * witness, we have var = 3, the intersection is of course
                 * empty. Try to find such values and replac'em by bigger
                 * ranges:
                 */
                final State witnessCand = curWitness.clone();

                final HeapPositions predHeapPositions = new HeapPositions(predecessorNode.getState(), true);
                final CollectionMap<AbstractVariableReference, StatePosition> predRefToPosition =
                    predHeapPositions.getReferencesAndPositions();
                for (final AbstractVariableReference predRef : predRefToPosition.keySet()) {
                    //Get random position for this reference:
                    final StatePosition pos = predRefToPosition.getNotNull(predRef).iterator().next();
                    final AbstractVariableReference witnessRef = witnessCand.getReference(pos);

                    if (predRef.pointsToAnyIntegerType()) {
                        final AbstractInt witnessVal = (AbstractInt) witnessCand.getAbstractVariable(witnessRef);
                        final AbstractInt predVal =
                            (AbstractInt) predecessorNode.getState().getAbstractVariable(predRef);
                        try {
                            predVal.intersect(witnessVal);
                        } catch (final IntersectionFailException ex) {
                            //This is one of the values where the intersection is empty. Try the old value:
                            //Setting a constant to another value would be stupid:
                            if (witnessRef.pointsToConstantInt()) {
                                witnessCand.removeAbstractVariable(predRef);
                                witnessCand.addAbstractVariable(predRef, predVal);
                                witnessCand.replaceReference(witnessRef, predRef);
                            } else {
                                witnessCand.removeAbstractVariable(witnessRef);
                                witnessCand.addAbstractVariable(witnessRef, predVal);
                            }
                        }
                    }
                }

                //Now try again with the new state:
                try {
                    newWitness = Intersector.intersect(witnessCand, predecessorState);
                } catch (final IntersectionFailException anotherFailExc) {
                    return null;
                }
            }
        } else if (edgeLabel instanceof InitializationStateChange) {
            final InitializationStateChange isc = (InitializationStateChange) edgeLabel;
            newWitness = curWitness.clone();
            final CallStack c = newWitness.getCallStack();
            final ClassInitializationInformation newInitState = newWitness.getClassInitInfo();
            for (final Triple<ClassName, InitStatus, InitStatus> p : isc.getNewInitStates()) {
                if (p.y == InitStatus.RUNNING) {
                    //drop the stack frame of the class loader
                    c.getStackFrameList().remove(0);
                }
                if (p.z == InitStatus.NO) {
                    //unload static fields
                    newWitness.getStaticFields().dropInformationAbout(p.x);
                }
                if (p.z == InitStatus.MAYBE) {
                    //maybe is the default value and leaving it explicit will be very, very bad, as not all parts of the code interpret it as such
                    newInitState.getClassesWithInitializationState(curWitness.getJBCOptions()).remove(p.x);
                } else {
                    newInitState.getClassesWithInitializationState(curWitness.getJBCOptions()).put(p.x, p.z);
                }
            }
        } else if (edgeLabel instanceof CallAbstractEdge) {
            /*
             * This is very much like handling a return after a recursive call:
             *  (1) Rename our witness to avoid name clashes
             *  (2) Take the source of the call abstract state (with all stack frames) and
             *    (a) Copy in all data from our witness
             *    (d) Set static fields to their values in our witness
             *    (b) Chop off the topmost stack frame
             *    (c) Add the stackframe(s) from our witness
             *    (e) Replace all input references in the abstracted states by their corresponding new versions
             *        from our (renamed) witness
             */
            final State renamedCurWitness = curWitness.clone();
            renamedCurWitness.replaceAllReferences();

            final State preparedPredState = predecessorState.clone();
            preparedPredState.addAllDataFrom(renamedCurWitness);
            for (final ClassName className : preparedPredState.getStaticFields().getClasses()) {
                for (final String fieldName : renamedCurWitness.getStaticFields().getNames(className)) {
                    final AbstractVariableReference ref = renamedCurWitness.getStaticFields().get(className, fieldName);
                    preparedPredState.getStaticFields().set(className, fieldName, ref);
                }
            }
            preparedPredState.getCallStack().pop();
            preparedPredState.addFrame(renamedCurWitness.getCallStack().getTop());

            final InputReferences predIRs = e.getEnd().getState().getInputReferences();
            for (final InputReference newInputRef : renamedCurWitness.getInputReferences()) {
                final InputReference oldInputRef = predIRs.getCorrespondingIR(newInputRef);
                preparedPredState.replaceReference(oldInputRef.getReference(), newInputRef.getReference());
            }

            //The IRs are now useless (in fact, they are computed when the CallAbstractEdge is inserted), so we remove them:
            preparedPredState.getCallStack().getTop().getInputReferences().clear();
            newWitness = preparedPredState;
        } else {
            throw new NotYetImplementedException();
        }

        newWitness.gc();
        return newWitness;
    }

    /**
     * If <code>concrState</code> is an instance of <code>abstrState</code>
     * and both states have the same number of positions, this method computes a
     * mapping from the references in <code>abstrState </code> to the ones from
     * <code>concrState</code>.
     *
     * @param concrState some abstract state
     * @param abstrState some state which is an instance of <code>abstrState
     * </code>
     * @return map between the references in <code>abstrState</code> and <code>
     *  concrState</code>.
     */
    public static Map<AbstractVariableReference, AbstractVariableReference> computeReferenceMapping(final State abstrState,
        final State concrState) {
        final Map<AbstractVariableReference, AbstractVariableReference> resMap = new LinkedHashMap<>();

        final HeapPositions abstrHeapPos = new HeapPositions(abstrState, true);
        final HeapPositions concrHeapPos = new HeapPositions(concrState, true);

        for (final AbstractVariableReference abstrR : abstrState.getReferences().keySet()) {
            if (abstrR.isNULLRef()) {
                continue;
            }
            final Collection<StatePosition> abstrRPositions = abstrHeapPos.getPositionsForRef(abstrR);
            final Set<AbstractVariableReference> concrRefs = new LinkedHashSet<>();
            for (final StatePosition abstrRPos : abstrRPositions) {
                final AbstractVariableReference concrRCand = concrHeapPos.getReferenceForPos(abstrRPos, true);
                assert (concrRCand != null) : "Abstract state has position that is not in concrete state!";
                concrRefs.add(concrRCand);
            }

            if (concrRefs.size() == 1) {
                resMap.put(abstrR, concrRefs.iterator().next());
            }
        }

        return resMap;
    }

    /**
     * Checks if the given state can potentially ignore any invariants.
     * There can be invariants our analysis does not know about, for example that a certain static/instance field is always > 5
     * 
     * This method checks if there are any such cases.
     * The two concrete invariants we check are that array lengths and the count field of strings must be integers >= 0
     * 
     * If there are any loaded static fields this method returns true.
     * If there are any (partially-) realised objects on the heap that are
     * not primitive nor String or a (potentially multidimensional) array of either this method returns true.
     * 
     * @param startState the state to check, usually the result of reverse Evaluation for Nontermination analysis
     * @return true if there could be ignored invariants in startState
     */
    public static boolean canIgnoreInvariants(State startState) {
        //each static field be an invariant, so we do not allow any static field to be loaded
        if (!startState.getStaticFields().getValues().isEmpty()) {
            return true;
        }

        //next go over all parameters
        Set<AbstractVariableReference> toCheck = startState.getReferences().keySet();
        for (AbstractVariableReference refToCheck : toCheck) {
            if (!refToCheck.pointsToReferenceType()) {
                continue; //primitive values are okay
            }
            AbstractVariable variable = startState.getAbstractVariable(refToCheck);
            if (variable == null) {
                continue; //no info, so no invariants can be ignored
            }
            AbstractType abstractType = startState.getHeapAnnotations().getAbstractType(refToCheck);
            Set<FuzzyType> possibleClasses = abstractType.getPossibleClassesCopy();
            if (possibleClasses.size() != 1) {
                return true; //no concrete info on the type but we need it
            }
            FuzzyType type = possibleClasses.iterator().next();
            if (variable instanceof Array) {
                //length must be >= 0
                AbstractVariableReference lengthRef = ((Array)variable).getLength();
                AbstractVariable length = startState.getAbstractVariable(lengthRef);
                if (length != null && ((AbstractInt)length).getLower().isNegative()) {
                    return true;
                }
                //the innermost type of the Array must be a primitive Type or String
                FuzzyType innermostType = type.getInnermostType();
                if (!isLegalType(innermostType, startState.getClassPath(), startState.getJBCOptions())) {
                    return true;
                }
                continue;
            } else if (variable instanceof AbstractInstance) {
                //there is no Info on AbstractInstances, so no invariants can be ignored here
                continue;
            } else if (variable instanceof ConcreteInstance) {
                if (!isLegalType(type, startState.getClassPath(), startState.getJBCOptions())) {
                    return true;
                }
                ConcreteInstance instance = (ConcreteInstance) variable;
                //count must be >= 0
                AbstractVariableReference countRef = instance.getField(ClassName.Important.JAVA_LANG_STRING.getClassName(), "count", true);
                AbstractVariable count = startState.getAbstractVariable(countRef);
                if (count != null && ((AbstractInt)count).getLower().isNegative()) {
                    return true;
                }
                //offset must be >= 0
                AbstractVariableReference offsetRef = instance.getField(ClassName.Important.JAVA_LANG_STRING.getClassName(), "offset", true);
                AbstractVariable offset = startState.getAbstractVariable(countRef);
                if (offset != null && ((AbstractInt)offset).getLower().isNegative()) {
                    return true;
                }
                continue;
            } else {
                return true; //unknown AbstractVariable
            }
        }
        return false;
    }

    /**
     * This is a type check for {@linkplain #canIgnoreInvariants(State)}
     * @param type The type to check
     * @param classPath the classpath for the analysis
     * @param options the options for the analysis
     * @return true when the expansion of the class is primitive or a String
     */
    private static boolean isLegalType(FuzzyType type, ClassPath classPath, JBCOptions options) {
        Set<FuzzyType> expanded = new HashSet<>();
        type.expand(expanded, classPath, options);
        if (expanded.size() != 1) {
            return false;
        }
        type = expanded.iterator().next();
        return type instanceof FuzzyPrimitiveType || type.equals(FuzzyClassType.FT_JAVA_LANG_STRING);
    }

    /**
     * @param witness some state which is supposedly a witness for
     * nontermination
     * @param stateToReach some other state which we want to reach (may be null,
     * then we search for a repetition and not for reachability).
     * @param interestingRefs map indicating all interesting references
     * @param progPosToGraphState map from program position to a corresponding state in the graph.
     * @param aborter the aborter, used to check if we still need to run
     * @return either a run (list of states) or NULL.
     * @throws AbortionException if we were aborted.
     */
    public static Pair<List<State>, Triple<Integer, Integer, Set<StatePosition>>> verifyWitness(final State witness,
        final State stateToReach,
        final InterestingReferences interestingRefs,
        final CollectionMap<OpCode, State> progPosToGraphState,
        final Abortion aborter,
        final JBCOptions jbcOptions) throws AbortionException {
        IMethod startMethod = witness.getTerminationGraph().getStartGraph().getParsedMethod();
        final List<State> res = new LinkedList<>();
        res.add(witness);

        //Clean up state to reach:
        if (stateToReach != null) {
            for (final StackFrame sf : stateToReach.getCallStack().getStackFrameList()) {
                sf.getInputReferences().clear();
            }
            stateToReach.gc();
        }

        /*
         * Some sanity checks:
         *  - The witness should have only stack frame.
         *  - The witness should be at first opcode.
         *  - If we start with main, the args[] argument may not be null or
         *    contain null pointers.
         */
        if (witness.getCallStack().size() > 1) {
            return null;
        }
        final StackFrame witnessTopFrame = witness.getCurrentStackFrame();
        if (witnessTopFrame.getCurrentOpCode().getPos() != 0) {
            return null;
        }

        if ("main".equals(startMethod.getMethodIdentifier().getMethodName())) {
            final AbstractVariableReference argsArrayRef = witnessTopFrame.getLocalVariable(0);
            //If its null, noone cares about it. Good.
            if (argsArrayRef != null) {
                if (argsArrayRef.isNULLRef()) {
                    return null;
                }
                final AbstractVariable argsArray = witness.getAbstractVariable(argsArrayRef);
                if (argsArray instanceof ConcreteArray) {
                    final ConcreteArray concrArgsArray = (ConcreteArray) argsArray;
                    for (final AbstractVariableReference content : concrArgsArray.getData()) {
                        if (content.isNULLRef()) {
                            return null;
                        }
                    }
                }
            }
        }

        final CollectionMap<OpCode, State> progPosToState = new CollectionMap<>();
        progPosToState.add(witness.getCurrentOpCode(), witness);

        final Map<State, Integer> stateToId = new LinkedHashMap<>();
        stateToId.put(witness, 0);

        State curState = witness;
        if (!curState.callStackEmpty()) {
            curState.getInputReferences().clear();
            curState.gc();
        }
        for (int i = 1; i <= JBCOptions.MAXIMAL_WITNESS_VERIFICATION_STEPS; i++) {
            aborter.checkAbortion();
            final LinkedList<Pair<State, ? extends EdgeInformation>> newStates = new LinkedList<>();

            //We reached a program end:
            if (curState.getCallStack().size() == 0) {
                return null;
            }

            final StackFrame currentFrame = curState.getCurrentStackFrame();
            OpCode currentOpCode = currentFrame.getCurrentOpCode();
            if (currentFrame.hasException()) {
                    OpCode.handleException(curState, newStates);
            } else {
                // maybe we need to refine information before we can evaluate
                boolean refined = currentOpCode.refine(curState, newStates);
                //Handle init refinements as special case: Always take the NO answer if there are 2:
                if (newStates.size() > 0 && newStates.iterator().next().y instanceof InitializationStateChange) {
                    State noCase = null;
                    State yesCase = null;
                    for (final Pair<State, ? extends EdgeInformation> p : newStates) {
                        final EdgeInformation e = p.y;
                        if (e instanceof InitializationStateChange) {
                            final InitializationStateChange isc = (InitializationStateChange) e;
                            final Collection<Triple<ClassName, InitStatus, InitStatus>> niss = isc.getNewInitStates();
                            assert niss.size()>0;
                            boolean allYes = true;
                            boolean allNo = true;
                            for (Triple<ClassName, InitStatus, InitStatus> nis : niss) {
                                if (nis.y != InitStatus.NO) {
                                    allNo = false;
                                } else if (nis.y != InitStatus.YES) {
                                    allYes = false;
                                }
                            }
                            if (allNo) {
                                //We found what we want
                                noCase = p.x;
                                break;
                            } else if (allYes) {
                                //Can't break yet because there still might be a no case
                                yesCase = p.x;
                            }
                        }
                    }
                    if (noCase != null) {
                        curState = noCase.getClassInitInfo().initializeNeededClasses(noCase).x;
                        currentOpCode = curState.getCurrentStackFrame().getCurrentOpCode();
                    } else if (yesCase != null) {
                        curState = yesCase;
                    } else {
                        //FAIL:
                        return null;
                    }
                    newStates.clear();
                } else {
                    if (refined) {
                        // Refinement should not be needed. FAIL:
                        return null;
                    }
                }
                Pair<State, ? extends EdgeInformation> evRes = currentOpCode.evaluate(curState);
                if (evRes != null) {
                    newStates.add(evRes);
                }
            }

            assert (newStates.size() == 1) : "Evaluation resulted in several successors!";

            curState = newStates.get(0).x;
            if (!curState.callStackEmpty()) {
                curState.gc();
                curState.getInputReferences().clear();
            }

            /*
             * Check if we have a recursion (i.e., one method appears twice in the stack). If yes, cut off the stack
             * below the topmost one:
             */
            if (!curState.getCallStack().isEmpty()) {
                //Check if we are at a method start (i.e., first opcode, stack below is call)
                final CallStack curCallStack = curState.getCallStack();
                if (curCallStack.size() > 1 && curCallStack.get(0).getCurrentOpCode().getPos() == 0
                    && curCallStack.get(1).getCurrentOpCode() instanceof InvokeMethod) {
                    //Check if we would split:
                    final IMethod topmostMethod = curCallStack.getTop().getMethod();
                    final HandlingMode handlingMode = curState.getTerminationGraph().getGoal();
                    if (MethodStart.shouldSplitMethodAnalysis(curCallStack.get(1), topmostMethod, jbcOptions, handlingMode)) {
                        while (curCallStack.size() > 1) {
                            curCallStack.getStackFrameList().remove(1);
                        }
                    }
                }
            }

            res.add(curState);
            stateToId.put(curState, i);

            //Check if we reached our target state:
            if (stateToReach != null) {
                if (new PathMerger().isInstance(curState, stateToReach)) {
                    return new Pair<>(res, null);
                }
            }

            //Check if we are repeating:
            final OpCode newOpcode = curState.getCurrentOpCode();
            nextPartner: for (final State oldState : progPosToState.getNotNull(newOpcode)) {
                //Check that the stack height matches:
                if (oldState.getCallStack().size() != curState.getCallStack().size()) {
                    continue nextPartner;
                }

                //Check that the init status is OK:
                final Map<ClassName, InitStatus> oldInitState =
                    oldState.getClassInitInfo().getClassesWithInitializationState(witness.getJBCOptions());
                for (final Entry<ClassName, InitStatus> e : curState.getClassInitInfo().getClassesWithInitializationState(witness.getJBCOptions()).entrySet()) {
                    if (!e.getValue().equals(oldInitState.get(e.getKey()))) {
                        continue nextPartner;
                    }
                }
                Set<AbstractVariableReference> interestingReferencesOld = new LinkedHashSet<>();
                final Set<StatePosition> interestingPositions = new LinkedHashSet<>();
                boolean foundOneHit = false;
                if (progPosToGraphState != null && interestingRefs != null) {
                    for (final State graphState : progPosToGraphState.getNotNull(newOpcode)) {
                        foundOneHit = true;
                        for (final StatePosition spos : interestingRefs.getInterestingPositions(graphState)) {
                            final AbstractVariableReference refInGraphState = spos.getFromState(graphState, true, null);
                            final AbstractVariableReference refInOldState = spos.getFromState(oldState, true, null);
                            if (refInGraphState != null && refInOldState == null) {
                                /*
                                 * [To the tune of Last Christmas]
                                 * Last termgraph,
                                 * I needed my ref
                                 * but the very next check
                                 * you gave it away
                                 * ...
                                 * In other words: We need this one. If it's away, we've lost - unless it's a static
                                 * field, because if it would be really needed, it would be around (it still appears
                                 * as interesting position sometimes if (by accident) an insteresting reference in the
                                 * graph also appears in that static field).
                                 * Furthermore we can by accident create intersting references that start in IRs,
                                 * and sorting them out here is cheaper than during construction of IRs.
                                 */
                                if (!(spos instanceof StaticFieldRootPosition) && !(spos.getRootPosition() instanceof InputRefRootPosition)) {
                                    continue nextPartner;
                                }
                            } else {
                                interestingPositions.add(spos);
                                interestingReferencesOld.add(refInOldState);
                            }
                        }
                    }
                }
                if (!foundOneHit) {
                    interestingReferencesOld = null;
                }

                if (new PathMerger().isInstance(curState, oldState, interestingReferencesOld)) {
                    return new Pair<>(res, new Triple<>(stateToId.get(oldState), i, interestingPositions));
                }
            }

            progPosToState.add(curState.getCurrentOpCode(), curState);
        }

        return null;
    }
}
