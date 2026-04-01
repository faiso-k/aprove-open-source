package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Gets a state and tries to generate a witness in the method graph.
 * @author Marc Brockschmidt
 */
public class LoopingNonTermWitnessFinder extends NonTermWorker {
    /**
     * Number of loop unrollings considered in the SMT proof step. In this step, we try to find some state such that
     * after 1 <= i <= NUMBER_OF_LOOP_UNROLLINGS loop runs, the integer values again have the same value. */
    static final int NUMBER_OF_LOOP_UNROLLINGS = 10;

    /**
     * The node which was reached a second time in the graph construction.
     */
    private final Node repeatingNode;

    /**
     * @param graph some method graph
     * @param repNode some node leading to a possible repetition.
     * @param iNode some node for which a witness (a state that is an instance of the method's start state) should be
     * generated.
     */
    private LoopingNonTermWitnessFinder(final MethodGraph graph, final Node repNode, final Node iNode) {
        super(graph, iNode);
        this.repeatingNode = repNode;
    }

    /** {@inheritDoc} */
    @Override
    public WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        /*
         * From our interesting node, we construct a witness by backwards
         * traversal of our termination graph until we reach the start state
         * of our method. At all times, we store which node in the graph
         * is representing our current proto-witness.
         */
        final Node curAbstrNode = this.getInterestingNode();

        //We only try to find early witnesses:
        if (curAbstrNode.getNodeNumber() > 1000000) {
            return WorkStatus.CONTINUE;
        }

        if (Globals.DEBUG_MARC) {
            System.err.println("Checking possible witness:\n" + curAbstrNode.getState());
            this.getMethodGraph().getTerminationGraph().dumpImage(false);
        }

        //Try to use SMT to get some information about the integer variables:
        this.getMethodGraph().getGraphLock().readLock().lock();

        final CollectionMap<OpCode, State> progPosToGraphState = new CollectionMap<>();
        Set<List<Edge>> paths = new LinkedHashSet<>();
        final Set<Edge> allEdges = new LinkedHashSet<>();
        try {
            //The recursive case:
            if (this.getMethodGraph().getStartNode().equals(curAbstrNode)) {
                for (final MethodEndListener listener : this.getMethodGraph().getMethodEndListeners()) {
                    if (listener.getMethodGraph().equals(this.getMethodGraph())) {
                        //We want the call abstract node of this call site:
                        for (final Edge outEdge : listener.getNode().getOutEdges()) {
                            if (outEdge.getLabel() instanceof CallAbstractEdge) {
                                final Node abstractedCallNode = outEdge.getEnd();
                                for (final List<Edge> path : JBCGraph.getAllPathsBetween(
                                    curAbstrNode,
                                    abstractedCallNode,
                                    NonTermWorker.getEdgeFilter(listener.getMethodGraph())))
                                {
                                    paths.add(path);
                                    allEdges.addAll(path);
                                }
                                allEdges
                                    .add(new Edge(abstractedCallNode, new InstanceEdge("call", false), curAbstrNode));
                                break;
                            }
                        }
                    }
                }
            } else {
                paths = JBCGraph.getAllPathsBetween(curAbstrNode, curAbstrNode, NonTermWorker.getEdgeFilter(this.getMethodGraph()));
                for (final List<Edge> path : paths) {
                    //Pop the cycle-closing instance edge away:
                    allEdges.addAll(path);
                    path.remove(path.size() - 1);
                }
            }
            paths = new LinkedHashSet<>(paths);
            final JBCGraph subgraph = JBCGraph.getSubGraphByEdges(allEdges);

            final InterestingReferences interestingRefs = new InterestingReferences(subgraph, true, aborter);

            boolean takeNodeFromLoop = false;
            nodeLoop: for (final Node n : subgraph.getNodes()) {
                for (final AbstractVariableReference ref : interestingRefs.getInterestingRefs(n.getState())) {
                    if (ref.pointsToReferenceType()) {
                        takeNodeFromLoop = true;
                        break nodeLoop;
                    }
                }
                final State s = n.getState();
                progPosToGraphState.add(s.getCurrentOpCode(), s);
            }

            /*
             * For each path, convert the edge labels into SMT constraints
             * (if possible).
             */
            final List<List<SMTLIBTheoryAtom>> allPathConstraints = new ArrayList<>();
            int pathNum = 0;
            final Iterator<List<Edge>> pathIt = paths.iterator();
            while (pathIt.hasNext()) {
                final List<Edge> path = pathIt.next();
                pathNum++;

                //Early fail if a return value of a skipped function is interesting:
                for (final Edge edge : path) {
                    final EdgeInformation label = edge.getLabel();
                    if (label instanceof MethodSkipEdge) {
                        final MethodSkipEdge mse = ((MethodSkipEdge) label);
                        final Node node = mse.getNode();
                        if (node == null) {
                            continue;
                        }
                        final State methodEndState = node.getState();
                        final FuzzyType returnType =
                            methodEndState
                                .getCurrentOpCode()
                                .getMethod()
                                .getMethodIdentifier()
                                .getDescriptor()
                                .getReturnType();
                        //method is void, we can go on:
                        if (returnType == null) {
                            continue;
                        }
                        //Otherwise, get new name for returned ref (was on top of opstack in returning state)
                        final AbstractVariableReference returnedRef =
                            mse.getReturningToResultMap().get(
                                methodEndState.getCurrentStackFrame().getOperandStack().peek(0));
                        if (interestingRefs.getInterestingRefs(edge.getEnd().getState()).contains(returnedRef)) {
                            return WorkStatus.CONTINUE;
                        }
                    }
                }

                //If we take the node from the loop, only use the formulas over that node:
                if (takeNodeFromLoop) {
                    boolean isNeeded = false;
                    for (final Edge edge : path) {
                        if (edge.getEnd().equals(this.repeatingNode) || edge.getStart().equals(this.repeatingNode)) {
                            isNeeded = true;
                        }
                    }
                    if (!isNeeded) {
                        pathIt.remove();
                        pathNum--;
                        continue;
                    }
                }

                final Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> p =
                    SMTUtilities.convertPathToSMTFormulas(path, interestingRefs, "path" + pathNum, false);
                //We don't need to differentiate:
                final List<SMTLIBTheoryAtom> pathComputations = p.x;
                pathComputations.addAll(p.y);

                allPathConstraints.add(pathComputations);
            }

            final List<Formula<SMTLIBTheoryAtom>> unrolledLoopConstraints = new LinkedList<>();
            final List<Formula<SMTLIBTheoryAtom>> stayedTheSameAfterUnrolling = new LinkedList<>();

            /*
             * Now prepare the unrollings: For every unrolling, connect the start
             * values to the values before (or the initial ones).
             */
            final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();
            for (int i = 1; i <= LoopingNonTermWitnessFinder.NUMBER_OF_LOOP_UNROLLINGS; i++) {
                final Edge selfEdge = new Edge(curAbstrNode, new InstanceEdge("tmp", false), curAbstrNode);

                final String thisUnrollLabel = "unroll" + i;
                final String nextUnrollLabel = "unroll" + (i + 1);

                Formula<SMTLIBTheoryAtom> thisUnrollFormula = factory.buildConstant(false);
                pathNum = 0;
                for (final List<Edge> path : paths) {
                    final List<SMTLIBTheoryAtom> templatePathConstraints = allPathConstraints.get(pathNum);
                    pathNum++;
                    final String pathLabel = "path" + pathNum;

                    final List<SMTLIBTheoryAtom> unrolledPathConstraints =
                        SMTUtilities.renameVariablesInSMTAtoms(
                            pathLabel,
                            thisUnrollLabel + pathLabel,
                            templatePathConstraints,
                            factory);

                    //Let all paths start with the same values:
                    unrolledPathConstraints.addAll(SMTUtilities.instanceEdgeToSMTAtoms(selfEdge, null, thisUnrollLabel
                        + "initial", thisUnrollLabel + pathLabel));

                    //Let all paths end with the same values:
                    final Node lastNode = path.get(path.size() - 1).getEnd();
                    final Edge iEdge = new Edge(lastNode, new InstanceEdge("tmp", false), curAbstrNode);
                    unrolledPathConstraints.addAll(SMTUtilities.instanceEdgeToSMTAtoms(
                        iEdge,
                        interestingRefs,
                        thisUnrollLabel + pathLabel,
                        nextUnrollLabel + "initial"));
                    thisUnrollFormula =
                        factory.buildOr(
                            thisUnrollFormula,
                            factory.buildAnd(factory.buildTheoryAtoms(unrolledPathConstraints)));
                }

                unrolledLoopConstraints.add(thisUnrollFormula);

                //The values at the end of the loop are the same as at the start:
                stayedTheSameAfterUnrolling.add(factory.buildAnd(factory.buildTheoryAtoms(SMTUtilities
                    .instanceEdgeToSMTAtoms(selfEdge, interestingRefs, "unroll1" + "initial", nextUnrollLabel
                        + "initial"))));
            }

            //Information about the start values:
            final List<SMTLIBTheoryAtom> loopInvariants =
                SMTUtilities.extractStateInvariants(curAbstrNode.getState(), "unroll1initial");

            List<Edge> pathFromStart =
                this
                    .getMethodGraph()
                    .getTerminationGraph()
                    .getPathFromStartToNode(this.getMethodGraph(), this.getInterestingNode());
            if (pathFromStart == null) {
                pathFromStart = Collections.<Edge>emptyList();
            }

            List<SMTLIBTheoryAtom> invariantAtCallSite = null;
            //Recursive case, try to find invariants at call site:
            if (this.getMethodGraph().getStartNode().equals(curAbstrNode)) {
                for (final MethodEndListener mel : this.getMethodGraph().getMethodEndListeners()) {
                    final Edge callConnectingEdge =
                        new Edge(mel.getNode(), new InstanceEdgeBetweenGraphs(), this.getInterestingNode());
                    invariantAtCallSite =
                        SMTUtilities.extractStateInvariants(mel.getNode().getState(), "unroll1initial");
                    final Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> instanceEdgeEnc =
                        SMTUtilities.convertPathToSMTFormulas(
                            Collections.singletonList(callConnectingEdge),
                            null,
                            "unroll1initial",
                            false);
                    invariantAtCallSite.addAll(instanceEdgeEnc.x);
                    invariantAtCallSite.addAll(instanceEdgeEnc.y);
                    break;
                }
            }

            final List<SMTLIBTheoryAtom> formulaForPathFromStart = new LinkedList<>();
            final Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> p =
                SMTUtilities.convertPathToSMTFormulas(pathFromStart, null, "unroll1initial", true);
            formulaForPathFromStart.addAll(p.x);
            formulaForPathFromStart.addAll(p.y);

            final Formula<SMTLIBTheoryAtom> loopingFormula =
                factory.buildAnd(
                    factory.buildAnd(unrolledLoopConstraints),
                    factory.buildOr(stayedTheSameAfterUnrolling));
            final Formula<SMTLIBTheoryAtom> loopingFormulaWithInitial =
                factory.buildAnd(loopingFormula, factory.buildAnd(factory.buildTheoryAtoms(loopInvariants)));
            final Formula<SMTLIBTheoryAtom> loopingFormulaWithInitialAndPathFromStart =
                factory.buildAnd(
                    loopingFormulaWithInitial,
                    factory.buildAnd(factory.buildTheoryAtoms(formulaForPathFromStart)));

            if (Globals.DEBUG_MARC) {
                this.getMethodGraph().getTerminationGraph().dumpImage(false);
            }
            final SMTEngine smtEngine = new SMTLIBEngine();
            Pair<YNM, Map<String, String>> res =
                    SMTUtilities.solve(loopingFormulaWithInitialAndPathFromStart, smtEngine, aborter, 1000);

            if (res.x != YNM.YES && invariantAtCallSite != null && !invariantAtCallSite.isEmpty()) {
                final Formula<SMTLIBTheoryAtom> loopingFormulaWithInvariantsFromCallSite =
                    factory.buildAnd(
                        loopingFormulaWithInitial,
                        factory.buildAnd(factory.buildTheoryAtoms(invariantAtCallSite)));

                res = SMTUtilities.solve(loopingFormulaWithInvariantsFromCallSite, smtEngine, aborter, 1000);

                if (res.x != YNM.YES) {
                    return WorkStatus.CONTINUE;
                }
            }

            if (res.x != YNM.YES) {
                res = SMTUtilities.solve(loopingFormulaWithInitial, smtEngine, aborter, 1000);

                if (res.x != YNM.YES) {
                    return WorkStatus.CONTINUE;
                }
            }

            final Map<AbstractVariableReference, Long> refAssignment;

            if (pathNum == 1) {
                refAssignment = SMTUtilities.extractVariableAssignment(res.y, "unroll1path1_");
            } else {
                refAssignment = SMTUtilities.extractVariableAssignment(res.y, "unroll1initial_");
                //keep only references marked as interesting
                Set<AbstractVariableReference> toKeep;
                if (takeNodeFromLoop) {
                    toKeep = interestingRefs.getInterestingRefs(repeatingNode.getState());
                } else {
                    toKeep = interestingRefs.getInterestingRefs(curAbstrNode.getState());
                }
                refAssignment.keySet().retainAll(toKeep);
            }

            final Collection<State> startWitnesses;
            if (takeNodeFromLoop) {
                startWitnesses =
                    WitnessUtilities.findStartStateWitnessesForState(
                        this.getMethodGraph(),
                        this.repeatingNode,
                        SMTUtilities.applyRefAssignmentToState(this.repeatingNode.getState(), refAssignment, false),
                        refAssignment,
                        false,
                        aborter);
            } else {
                startWitnesses =
                    WitnessUtilities.findStartStateWitnessesForState(
                        this.getMethodGraph(),
                        curAbstrNode,
                        SMTUtilities.applyRefAssignmentToState(curAbstrNode.getState(), refAssignment, false),
                        refAssignment,
                        false,
                        aborter);
            }

            for (final State startWitness : startWitnesses) {
                Pair<List<State>, Triple<Integer, Integer, Set<StatePosition>>> run =
                    WitnessUtilities.verifyWitness(
                        startWitness,
                        null,
                        interestingRefs,
                        progPosToGraphState,
                        aborter,
                        this.getMethodGraph().getJBCOptions());
                if (run == null) {
                    //Try again, but try to make the input array concrete:
                    final AbstractVariableReference argArrayRef =
                        startWitness.getCurrentStackFrame().getLocalVariable(0);
                    if (startWitness.getAbstractVariable(argArrayRef) instanceof AbstractArray) {
                        final State startWitnessCopy = startWitness.clone();
                        final AbstractVariableReference zeroRef =
                            startWitnessCopy.createReferenceAndAdd(AbstractInt.create(0), OperandType.INTEGER);
                        final FuzzyType inputArgsType =
                            new FuzzyClassType(ClassName.Important.JAVA_LANG_STRING.getClassName(), true, 1);
                        final AbstractVariableReference concrArgArrayRef =
                            startWitnessCopy.createReferenceAndAdd(new ConcreteArray(
                                zeroRef,
                                startWitnessCopy,
                                inputArgsType), OperandType.ARRAY);
                        startWitnessCopy.replaceReference(argArrayRef, concrArgArrayRef);
                        startWitnessCopy.gc();

                        //Try again:
                        run =
                            WitnessUtilities.verifyWitness(
                                startWitnessCopy,
                                null,
                                interestingRefs,
                                progPosToGraphState,
                                aborter,
                                this.getMethodGraph().getJBCOptions());
                        if (run == null) {
                            continue;
                        }
                    } else {
                        continue;
                    }
                }

                this
                    .getMethodGraph()
                    .getTerminationGraph()
                    .setNontermWitness(new LoopingNonTermWitness(run.x, run.y.x, run.y.y, run.y.z));
                return WorkStatus.FINISH;
            }

            return WorkStatus.CONTINUE;
        } finally {
            this.getMethodGraph().getGraphLock().readLock().unlock();
        }
    }

    /**
     * Create a new NonTerm worker and remember it, so that it is run when all graphs are finished.
     * @param graph some method graph
     * @param repNode some node leading to a possible repetition.
     * @param iNode some node for which a witness (a state that is an instance of the method's start state) should be
     * generated.
     */
    public static void runWhenFinished(final MethodGraph graph, final Node repNode, final Node iNode) {
        graph.queueNonTermWorker(new LoopingNonTermWitnessFinder(graph, repNode, iNode));
    }

    /**
     * Create a worker and add it to the given queue (so that it is run as one of the next jobs).
     * @param graph some method graph
     * @param repNode some node leading to a possible repetition.
     * @param iNode some node for which a witness (a state that is an instance of the method's start state) should be
     * generated.
     * @param newWorkers workers that will be run as one of the next jobs, NonTerm worker will be added here
     */
    public static void runNow(
        final MethodGraph graph,
        final Node repNode,
        final Node iNode,
        final Collection<MethodGraphWorker> newWorkers)
    {
        newWorkers.add(new LoopingNonTermWitnessFinder(graph, repNode, iNode));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.repeatingNode == null) ? 0 : this.repeatingNode.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LoopingNonTermWitnessFinder other = (LoopingNonTermWitnessFinder) obj;
        if (this.repeatingNode == null) {
            if (other.repeatingNode != null) {
                return false;
            }
        } else if (!this.repeatingNode.equals(other.repeatingNode)) {
            return false;
        }
        return true;
    }
}
