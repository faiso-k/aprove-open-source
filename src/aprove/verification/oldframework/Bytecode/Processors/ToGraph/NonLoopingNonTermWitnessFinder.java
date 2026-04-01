package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.*;
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
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 * Worker that tries to prove that a program is non-terminating by finding some
 * loop for which it can prove that (1) it's control flow is entirely determined
 * by integer values (2) there is no assignment to the integer variables such
 * that the loop condition(s) hold, but after one execution of the body, the
 * loop condition(s) do not hold anymore. It then extracts an assignment for the
 * variables in this loop and then tries to prove reachability of this assigment
 * from the program start.
 * @author Marc Brockschmidt
 */
public class NonLoopingNonTermWitnessFinder extends NonTermWorker {
    /** The head of the loop we are looking at. */
    private final Node loopStartNode;

    /**
     * @param graph some method graph
     * @param iNode some node for which we suspect that is is part of a non-
     * looping nonterminating loop.
     * @param lSNode head of the loop we are looking at.
     */
    private NonLoopingNonTermWitnessFinder(final MethodGraph graph, final Node iNode, final Node lSNode) {
        super(graph, iNode);
        this.loopStartNode = lSNode;
    }

    @Override
    public WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        final MethodGraph graph = this.getMethodGraph();
        final Node iNode = this.getInterestingNode();

        //If the nodes are gone, don't continue
        if (!graph.containsNode(iNode) || !graph.containsNode(this.loopStartNode)) {
            return WorkStatus.CONTINUE;
        }

        graph.getGraphLock().readLock().lock();
        try {
            Set<List<Edge>> paths = new LinkedHashSet<>();
            final Set<Edge> allEdges = new LinkedHashSet<>();
            //We need to add these edges explicitly later on as they are not contained in the normal graph structure:
            final Set<Edge> recursionClosingEdges = new LinkedHashSet<>();
            //The recursive case:
            if (this.getMethodGraph().getStartNode().equals(iNode)) {
                for (final MethodEndListener listener : this.getMethodGraph().getMethodEndListeners()) {
                    if (listener.getMethodGraph().equals(this.getMethodGraph())) {
                        //We want the call abstract node of this call site:
                        for (final Edge outEdge : listener.getNode().getOutEdges()) {
                            if (outEdge.getLabel() instanceof CallAbstractEdge) {
                                final Node abstractedCallNode = outEdge.getEnd();
                                for (final List<Edge> path : JBCGraph.getAllPathsBetween(
                                    iNode,
                                    abstractedCallNode,
                                    NonTermWorker.getEdgeFilter(listener.getMethodGraph())))
                                {
                                    paths.add(path);
                                    allEdges.addAll(path);
                                }
                                recursionClosingEdges.add(new Edge(
                                    abstractedCallNode,
                                    new InstanceEdgeBetweenGraphs(),
                                    iNode));
                                break;
                            }
                        }
                    }
                }
            } else {
                paths =
                    JBCGraph.getAllPathsBetween(
                        this.loopStartNode,
                        this.loopStartNode,
                        NonTermWorker.getEdgeFilter(this.getMethodGraph()));
                for (final List<Edge> path : paths) {
                    //Pop the cycle-closing instance edge away:
                    allEdges.addAll(path);
                    path.remove(path.size() - 1);
                }
            }
            paths = new LinkedHashSet<>(paths);

            //Compute subgraph and interesting references:
            final DontCrossNodesEdgeFilter loopHeadNodeFilter =
                new DontCrossNodesEdgeFilter(Collections.singleton(this.loopStartNode), graph);
            final Set<Node> allIncludedNodes = new LinkedHashSet<>();
            for (final List<Edge> path : paths) {
                for (final Edge e : path) {
                    allIncludedNodes.add(e.getStart());
                }
            }
            if (Globals.DEBUG_MARC) {
                this.getMethodGraph().getTerminationGraph().dumpImage(false);
            }
            //First try to find those paths that we can actually handle:
            final Iterator<List<Edge>> pathIt = paths.iterator();
            nextPath: while (pathIt.hasNext()) {
                final List<Edge> path = pathIt.next();
                for (final Edge e : path) {
                    //We cannot handle skipping other non-pure methods:
                    final EdgeInformation label = e.getLabel();
                    if (label instanceof MethodSkipEdge && !((MethodSkipEdge) label).callIsPure()) {
                        pathIt.remove();
                        continue nextPath;
                    }
                    final Node edgeStartNode = e.getStart();

                    /*
                     * Is there a non-empty path from the current node to itself without going through the loop head
                     * node? If so, we have a subcycle which we cannot handle.
                     */
                    if (JBCGraph.hasPath(edgeStartNode, edgeStartNode, false, loopHeadNodeFilter)) {
                        pathIt.remove();
                        continue nextPath;
                    }

                    /*
                     * We ensure that only the designated loop start node is reached from the outside. This allows
                     * several assumptions for the rest of the code, including that reference names are unique on a
                     * path.
                     */
                    if (!edgeStartNode.equals(this.loopStartNode)) {
                        for (final Edge inEdge : edgeStartNode.getInEdges()) {
                            if (!allIncludedNodes.contains(inEdge.getStart()) && paths.size() > 1) {
                                pathIt.remove();
                                continue nextPath;
                            }
                        }
                    }
                }
                allEdges.addAll(path);
            }
            if (paths.isEmpty()) {
                return WorkStatus.CONTINUE;
            }
            final JBCGraph subgraph = JBCGraph.getSubGraphByEdges(allEdges);
            for (final Edge e : recursionClosingEdges) {
                subgraph.createCopiedEdge(e);
            }

            final InterestingReferences interestingRefs = new InterestingReferences(subgraph, true, aborter);
            for (final Node node : subgraph.getNodes()) {
                //Check all interesting refs in all node for integer-ness:
                final Set<AbstractVariableReference> stateInterestingRefs =
                    interestingRefs.getInterestingRefs(node.getState());
                for (final AbstractVariableReference ref : stateInterestingRefs) {
                    if (!ref.pointsToAnyIntegerType()) {
                        //Not an int, SMT approach doesn't work.
                        return WorkStatus.CONTINUE;
                    }
                }
            }
            final State loopStartState = this.loopStartNode.getState();

            //This holds the path constraints, where each path gets its own vars:
            final List<List<SMTLIBTheoryAtom>> allPathComputations = new ArrayList<>();
            final List<List<SMTLIBTheoryAtom>> allPathConditions = new ArrayList<>();
            //This holds the constraints for the next loop, vars all using the prefix "res"
            final List<List<SMTLIBTheoryAtom>> allNextLoopComputations = new ArrayList<>();
            final List<List<SMTLIBTheoryAtom>> allNextLoopConditions = new ArrayList<>();

            /*
             * For each path, convert the edge labels into SMT constraints
             * (if possible). Then connect the values at the end of the loop to
             * the variables at the beginning of the next loop run. Also adds
             * equalities that ensure that all path formulas start with the same
             * start values.
             */
            int pathNum = 1;
            for (final List<Edge> path : paths) {
                final Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> p =
                    SMTUtilities.convertPathToSMTFormulas(path, interestingRefs, "template", false);

                final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();

                final List<SMTLIBTheoryAtom> pathComputations =
                    SMTUtilities.renameVariablesInSMTAtoms("template", "path" + pathNum, p.x, factory);
                allPathComputations.add(pathComputations);
                allPathConditions.add(SMTUtilities
                    .renameVariablesInSMTAtoms("template", "path" + pathNum, p.y, factory));
                final List<SMTLIBTheoryAtom> nextLoopComputations =
                        SMTUtilities.renameVariablesInSMTAtoms("template", "res" + pathNum, p.x, factory);
                allNextLoopComputations.add(nextLoopComputations);
                allNextLoopConditions.add(SMTUtilities.renameVariablesInSMTAtoms("template", "res" + pathNum, p.y, factory));

                //The last node on the path, an instance of the start node:
                final Node lastNode = path.get(path.size() - 1).getEnd();

                //These constraints connect the results of the first run with the
                //variables in between first and second run
                final Edge iEdge = new Edge(lastNode, new InstanceEdge("tmp", false), this.loopStartNode);
                pathComputations.addAll(SMTUtilities.instanceEdgeToSMTAtoms(
                    iEdge,
                    interestingRefs,
                    "path" + pathNum,
                    "res"));

                //These constraints connect the in between values to the variables in
                //the second run
                final Edge selfEdge = new Edge(this.loopStartNode, new InstanceEdge("tmp", false), this.loopStartNode);
                nextLoopComputations.addAll(SMTUtilities.instanceEdgeToSMTAtoms(
                    selfEdge,
                    interestingRefs,
                    "res",
                    "res" + pathNum));

                //These constraints connect the initial values to the variables in
                //this run:
                pathComputations.addAll(SMTUtilities.instanceEdgeToSMTAtoms(
                    selfEdge,
                    interestingRefs,
                    "path" + pathNum,
                    "initial"));

                pathNum++;
            }

            //Extra step: Split formulas with != to two formulas:
            int expandedNeq = 0;
            for (int pathID = 0; pathID < allPathComputations.size(); pathID++) {
                final List<SMTLIBTheoryAtom> pathComputations = allPathComputations.get(pathID);
                final List<SMTLIBTheoryAtom> pathConditions = allPathConditions.get(pathID);
                final ListIterator<SMTLIBTheoryAtom> condIt = pathConditions.listIterator();
                while (condIt.hasNext()) {
                    final SMTLIBTheoryAtom cond = condIt.next();
                    if (expandedNeq <= 1 && cond instanceof SMTLIBIntUnequal) {
                        final SMTLIBIntUnequal uneq = (SMTLIBIntUnequal) cond;
                        expandedNeq++;
                        //Create copies:
                        final SMTLIBTheoryAtom ltCond = SMTLIBIntLT.create(uneq.getA(), uneq.getB());
                        final SMTLIBTheoryAtom gtCond = SMTLIBIntGT.create(uneq.getA(), uneq.getB());

                        //Create copy of the conditions here, without uneq:
                        final LinkedList<SMTLIBTheoryAtom> ltPathConditions = new LinkedList<>(pathConditions);
                        ltPathConditions.remove(uneq);
                        ltPathConditions.add(ltCond);
                        final LinkedList<SMTLIBTheoryAtom> gtPathConditions = new LinkedList<>(pathConditions);
                        gtPathConditions.remove(uneq);
                        gtPathConditions.add(gtCond);

                        //Add the new Lists:
                        allPathComputations.add(pathComputations);
                        allPathConditions.add(ltPathConditions);
                        allPathComputations.add(pathComputations);
                        allPathConditions.add(gtPathConditions);
                        //next Loop
                        final List<SMTLIBTheoryAtom> nextLoopComp = allNextLoopComputations.get(pathID);
                        final List<SMTLIBTheoryAtom> nextLoopCond = allNextLoopConditions.get(pathID);
                        SMTLIBTheoryAtom atom = nextLoopCond.get(condIt.previousIndex());
                        assert atom instanceof SMTLIBIntUnequal;
                        SMTLIBIntUnequal nextUneq = (SMTLIBIntUnequal) atom;
                        //Create copies:
                        final SMTLIBTheoryAtom nextLtCond = SMTLIBIntLT.create(nextUneq.getA(), nextUneq.getB());
                        final SMTLIBTheoryAtom nextGtCond = SMTLIBIntGT.create(nextUneq.getA(), nextUneq.getB());
                        //Create copy of the conditions here, without uneq:
                        final LinkedList<SMTLIBTheoryAtom> ltNextLoopConditions = new LinkedList<>(nextLoopCond);
                        ltNextLoopConditions.remove(nextUneq);
                        ltNextLoopConditions.add(nextLtCond);
                        final LinkedList<SMTLIBTheoryAtom> gtNextLoopConditions = new LinkedList<>(nextLoopCond);
                        gtNextLoopConditions.remove(nextUneq);
                        gtNextLoopConditions.add(nextGtCond);
                        //Add the new Lists:
                        allNextLoopComputations.add(nextLoopComp);
                        allNextLoopConditions.add(ltNextLoopConditions);
                        allNextLoopComputations.add(nextLoopComp);
                        allNextLoopConditions.add(gtNextLoopConditions);
                    }
                }
            }

            //Information about the start values:
            final List<SMTLIBTheoryAtom> loopInvariants =
                SMTUtilities.extractStateInvariants(loopStartState, "initial");

            /*
             * Now build the actual formula:
             * Let
             *  \phi_1, ..., \phi_n describe the arithmetic conditions on all n
             *                      paths through the loop, each using their own
             *                      variables
             *  \psi_1, ..., \psi_n describe the computations on all n paths
             *  \phi_i', \psi_i' are the same, but using all the same variables
             *  (and let \psi_i contain equalities connecting the variables at the
             *   end of the loop body to the variables at the start of the loop)
             * Then, if
             *  ( (\psi_1 && \phi_1) ||
             *      ... ||
             *    (\psi_n && \phi_n)
             *  ) &&
             *  ( (\psi_1' && !\phi_1') &&
             *      ... &&
             *    (\psi_n' && !\phi_n'))
             * is UNSAT, there is no assignment to the variables of the loop such
             * that it runs once, but not again. Implies nontermination.
             */
            final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();
            final List<Formula<SMTLIBTheoryAtom>> firstRunFormulas = new ArrayList<>(allPathComputations.size());
            final List<Formula<SMTLIBTheoryAtom>> secondRunFormulas = new ArrayList<>(allPathComputations.size());

            final Formula<SMTLIBTheoryAtom> invariantFormula =
                factory.buildAnd(factory.buildTheoryAtoms(loopInvariants));

            //Create the set of all formula IDs and needed formulas:
            final Set<Integer> pathIDs = new TreeSet<>();
            for (int pathID = 0; pathID < allPathComputations.size(); pathID++) {
                pathIDs.add(pathID);
                final List<SMTLIBTheoryAtom> pathComputations = allPathComputations.get(pathID);
                final List<SMTLIBTheoryAtom> pathConditions = allPathConditions.get(pathID);
                firstRunFormulas.add(factory.buildAnd(
                    factory.buildAnd(factory.buildTheoryAtoms(pathComputations)),
                    factory.buildAnd(factory.buildTheoryAtoms(pathConditions))));

                final List<SMTLIBTheoryAtom> nextRunComputations = allNextLoopComputations.get(pathID);
                final List<SMTLIBTheoryAtom> nextRunConditions = allNextLoopConditions.get(pathID);

                secondRunFormulas.add(factory.buildAnd(
                    factory.buildAnd(factory.buildTheoryAtoms(nextRunComputations)),
                    factory.buildNot(factory.buildAnd(factory.buildTheoryAtoms(nextRunConditions)))));
            }

            final SMTEngine smtEngine = new SMTLIBEngine();

            //Now enumerate all possible combinations of the paths:
            final PowerSet<Integer> powSet = new PowerSet<>(ImmutableCreator.create(pathIDs), pathIDs.size(), true);
            Set<Integer> winningCombination = null;
            Formula<SMTLIBTheoryAtom> winningFormula = null;
            final Iterator<Set<Integer>> powSetIterator = powSet.iterator();

            while (powSetIterator.hasNext()) {
                final Set<Integer> pathCombination = powSetIterator.next();
                if (pathCombination.isEmpty()) {
                    continue;
                }

                final List<Formula<SMTLIBTheoryAtom>> firstRunFormulaCombination = new LinkedList<>();
                final List<Formula<SMTLIBTheoryAtom>> secondRunFormulaCombination = new LinkedList<>();

                for (final Integer pathId : pathCombination) {
                    firstRunFormulaCombination.add(firstRunFormulas.get(pathId));
                    secondRunFormulaCombination.add(secondRunFormulas.get(pathId));
                }

                final Formula<SMTLIBTheoryAtom> formula =
                    factory.buildAnd(
                        invariantFormula,
                        factory.buildAnd(
                            factory.buildOr(firstRunFormulaCombination),
                            factory.buildAnd(secondRunFormulaCombination)));

                //This call will NOT put results into the formula.
                Pair<YNM, Map<String, String>> res = SMTUtilities.solve(formula, smtEngine, aborter, 1000);
                //If the formula is UNSAT, we have a winner. Find an assignment:
                if (res.x == YNM.NO) {
                    winningCombination = pathCombination;
                    winningFormula = formula;
                    break;
                }
            }

            //No path combination did the job.
            if (winningFormula == null) {
                return WorkStatus.CONTINUE;
            }

            /*
             * For the assignment, add the conditions on the path from the start
             * node to the loop head.
             */
            List<Edge> pathFromStart =
                this
                    .getMethodGraph()
                    .getTerminationGraph()
                    .getPathFromStartToNode(this.getMethodGraph(), this.loopStartNode);
            if (pathFromStart == null) {
                pathFromStart = Collections.<Edge>emptyList();
            }

            final Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> p =
                SMTUtilities.convertPathToSMTFormulas(pathFromStart, null, "initial", false);
            final Formula<SMTLIBTheoryAtom> initialComputationFormula = factory.buildAnd(factory.buildTheoryAtoms(p.x));
            final Formula<SMTLIBTheoryAtom> initialConditionFormula = factory.buildAnd(factory.buildTheoryAtoms(p.y));

            final Formula<SMTLIBTheoryAtom> initialFormula =
                factory
                    .buildAnd(initialComputationFormula, factory.buildAnd(initialConditionFormula, invariantFormula));

            final YicesEngine.Arguments yicesArgs = new YicesEngine.Arguments();
            yicesArgs.ARGUMENTS = "--rand-seed=463345727";
            final SMTEngine yicesEngine = new YicesEngine(yicesArgs);
            Map<String, String> varAssignment = null;
            for (final Integer pathId : winningCombination) {
                final Formula<SMTLIBTheoryAtom> pathFormula = firstRunFormulas.get(pathId);
                final Formula<SMTLIBTheoryAtom> formula = factory.buildAnd(initialFormula, pathFormula);

                final SMTLIBIsNonLinearChecker nonLinearityChecker = new SMTLIBIsNonLinearChecker();
                formula.apply(nonLinearityChecker);

                //Try using the conditions on the path, too:
                Pair<YNM, Map<String, String>> res = SMTUtilities.solve(formula, yicesEngine, nonLinearityChecker, aborter);
                if (res.x == YNM.MAYBE) {
                    // try z3?
                    res = SMTUtilities.solve(formula, smtEngine, nonLinearityChecker, aborter);
                }
                if (res.x == YNM.YES) {
                    varAssignment = res.y;
                    break;
                }
            }
            if (varAssignment == null) {
                //Did not work. Only try the current conditions:
                for (final Integer pathId : winningCombination) {
                    final Formula<SMTLIBTheoryAtom> pathFormula = firstRunFormulas.get(pathId);
                    final Formula<SMTLIBTheoryAtom> formula = factory.buildAnd(invariantFormula, pathFormula);

                    final SMTLIBIsNonLinearChecker nonLinearityChecker = new SMTLIBIsNonLinearChecker();
                     formula.apply(nonLinearityChecker);

                    Pair<YNM, Map<String, String>> res = SMTUtilities.solve(formula, yicesEngine, nonLinearityChecker, aborter);
                    if (res.x == YNM.MAYBE) {
                        // try z3?
                        res = SMTUtilities.solve(formula, smtEngine, nonLinearityChecker, aborter);
                    }
                    if (res.x == YNM.YES) {
                        varAssignment = res.y;
                        break;
                    }
                }
            }

            //Darn, could not find _any_ var assignment that satisfies the loop conditions.
            if (varAssignment == null) {
                return WorkStatus.CONTINUE;
            }

            //Take the loop head, fill in values:
            final Map<AbstractVariableReference, Long> refAssignment =
                SMTUtilities.extractVariableAssignment(varAssignment, "initial_");
            final State loopStartWitness = SMTUtilities.applyRefAssignmentToState(loopStartState, refAssignment, true);

            final Collection<State> startStateWitnesses =
                WitnessUtilities.findStartStateWitnessesForState(
                    this.getMethodGraph(),
                    this.loopStartNode,
                    loopStartWitness,
                    refAssignment,
                    true,
                    aborter);

            if (startStateWitnesses == null) {
                return WorkStatus.CONTINUE;
            }

            // try to verify all found (possible) witnesses
            for (final State startStateWitness : startStateWitnesses) {
                Pair<List<State>, Triple<Integer, Integer, Set<StatePosition>>> r =
                    WitnessUtilities.verifyWitness(
                        startStateWitness,
                        loopStartWitness,
                        interestingRefs,
                        null,
                        aborter,
                        this.getMethodGraph().getJBCOptions());
                if (r == null) {
                    //Try again, but try to make the input array concrete:
                    final AbstractVariableReference argArrayRef =
                        startStateWitness.getCurrentStackFrame().getLocalVariable(0);
                    if (startStateWitness.getAbstractVariable(argArrayRef) instanceof AbstractArray) {
                        final State startStateWitnessCopy = startStateWitness.clone();
                        final AbstractVariableReference zeroRef =
                            startStateWitnessCopy.createReferenceAndAdd(AbstractInt.create(0), OperandType.INTEGER);
                        final FuzzyType inputArgsType =
                            new FuzzyClassType(ClassName.Important.JAVA_LANG_STRING.getClassName(), true, 1);
                        final AbstractVariableReference concrArgArrayRef =
                            startStateWitnessCopy.createReferenceAndAdd(new ConcreteArray(
                                zeroRef,
                                startStateWitnessCopy,
                                inputArgsType), OperandType.ARRAY);
                        startStateWitnessCopy.replaceReference(argArrayRef, concrArgArrayRef);
                        startStateWitnessCopy.gc();

                        //Try again:
                        r =
                            WitnessUtilities.verifyWitness(
                                startStateWitnessCopy,
                                loopStartWitness,
                                interestingRefs,
                                null,
                                aborter,
                                this.getMethodGraph().getJBCOptions());
                        if (r == null) {
                            continue;
                        }
                    } else {
                        continue;
                    }
                }
                final List<State> run = r.x;

                final Set<AbstractVariableReference> loopHeadInterestingRefs =
                    interestingRefs.getInterestingRefs(loopStartState);
                this
                    .getMethodGraph()
                    .getTerminationGraph()
                    .setNontermWitness(
                        new NonLoopingNonTermWitness(run, loopHeadInterestingRefs, winningFormula, loopStartState));

                return WorkStatus.FINISH;
            }
            return WorkStatus.CONTINUE;
        } finally {
            graph.getGraphLock().readLock().unlock();
        }
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
        newWorkers.add(new NonLoopingNonTermWitnessFinder(graph, repNode, iNode));
    }

    /**
     * Create a new NonTerm worker and remember it, so that it is run when all graphs are finished.
     * @param graph some method graph
     * @param repNode some node leading to a possible repetition.
     * @param iNode some node for which a witness (a state that is an instance of the method's start state) should be
     * generated.
     */
    public static void runWhenFinished(final MethodGraph graph, final Node repNode, final Node iNode) {
        graph.queueNonTermWorker(new NonLoopingNonTermWitnessFinder(graph, repNode, iNode));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.loopStartNode == null) ? 0 : this.loopStartNode.hashCode());
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
        final NonLoopingNonTermWitnessFinder other = (NonLoopingNonTermWitnessFinder) obj;
        if (this.loopStartNode == null) {
            if (other.loopStartNode != null) {
                return false;
            }
        } else if (!this.loopStartNode.equals(other.loopStartNode)) {
            return false;
        }
        return true;
    }
}
