package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * SimpleHeuristic.<br><br>
 *
 * Created: Feb 1, 2007<br>
 * Last modified: Feb 1, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class TerminationHeuristic extends AbstractGraphBuilderHeuristic {

    /**
     * The standard nested depth for generalization.
     */
    public static final int STANDARD_GENERALIZATION_DEPTH = 7;

    /**
     * The standard policy for generalizing all but one or only the
     * last constructor term.
     */
    public static final int STANDARD_GENERALIZATION_POSITION = 2;

    public static final int STANDARD_MAX_BRANCHING_FACTOR = 3;

    /**
     * Default value for minimal number of evaluations before hard abstractions are applied.
     */
    public static final int STANDARD_MIN_EX_STEPS = 2;

    public static final boolean STANDARD_NO_GROUND_LOSS = false;

    /**
     * For debugging.
     */
    private static final boolean DEBUG = false;

    //    private int steps = 0; // DEBUG STUFF

    private final int minExSteps;
    private final boolean noGroundLoss;

    public TerminationHeuristic() {
        this(
            TerminationHeuristic.STANDARD_MIN_EX_STEPS,
            TerminationHeuristic.STANDARD_GENERALIZATION_DEPTH,
            TerminationHeuristic.STANDARD_GENERALIZATION_POSITION,
            TerminationHeuristic.STANDARD_MAX_BRANCHING_FACTOR,
            TerminationHeuristic.STANDARD_NO_GROUND_LOSS);
    }

    public TerminationHeuristic(
        final int minExSteps,
        final int generalizationDepth,
        final int generalizationPosition,
        final int maxBranchingFactor)
    {
        this(
            minExSteps,
            generalizationDepth,
            generalizationPosition,
            maxBranchingFactor,
            TerminationHeuristic.STANDARD_NO_GROUND_LOSS);
    }

    public TerminationHeuristic(
        final int minExSteps,
        final int generalizationDepth,
        final int generalizationPosition,
        final int maxBranchingFactor,
        final boolean noGroundLoss)
    {
        super(generalizationDepth, generalizationPosition, maxBranchingFactor);
        if (minExSteps < 1) {
            throw new IllegalArgumentException("Minimal number of evaluations must be positive!");
        }
        if (generalizationDepth < 2) {
            throw new IllegalArgumentException("Generalization depth must be bigger than 1!");
        }
        this.minExSteps = minExSteps;
        this.noGroundLoss = noGroundLoss;
    }

    /**
     * @param graph
     * @param recursivePredicates
     * @param node
     * @param aborter
     * @param b
     * @throws AbortionException
     */
    @Override
    protected boolean expand(
        final PrologEvaluationGraph graph,
        final Set<Integer> recursiveClauses,
        final Map<FunctionSymbol, Integer> recursivePredicates,
        final Node<PrologAbstractState> node,
        final int numberOfExSteps,
        final Abortion aborter) throws AbortionException
    {
        // DEBUG STUFF
        //        this.steps++;
        //        if (steps > 20) {
        //            return;
        //        }
        //        System.err.println(this.steps);
        //        if (this.steps % 50 == 0) {
        //            graph.show();
        //        }
        //        if (this.steps == 100) {
        //            graph.show();
        //        }
        //        if (node.getNodeNumber() == 11) {
        //            System.err.println("Here!");
        //        }
        //        if (TerminationHeuristic.DEBUG) {
        //            graph.show();
        //        }
        // END DEBUG STUFF
        final PrologAbstractState currentState = node.getObject();
        if (currentState.isEmpty()) { // a leaf is a leaf is a leaf
            return true;
        }
        Node<PrologAbstractState> nextNode = graph.expandSuccess(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextNode = graph.expandFailure(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextNode = graph.expandUndefinedError(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextNode = graph.expandVariableError(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextNode = graph.expandCut(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextNode = graph.expandUnifyFail(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextNode = graph.expandBacktrack(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> nextPair = graph.expandUnify(node);
        aborter.checkAbortion();
        if (nextPair != null) {
            if (this.expand(graph, recursiveClauses, recursivePredicates, nextPair.x, numberOfExSteps, aborter)) {
                if (nextPair.y != null) {
                    aborter.checkAbortion();
                    return this.expand(
                        graph,
                        recursiveClauses,
                        recursivePredicates,
                        nextPair.y,
                        numberOfExSteps,
                        aborter);
                }
                return true;
            }
        }
        Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Node<PrologAbstractState>> nextTriple =
            graph.expandIs(node, aborter);
        aborter.checkAbortion();
        if (nextTriple != null) {
            if(nextTriple.x != null) {
                if(!this.expand(graph, recursiveClauses, recursivePredicates, nextTriple.x, numberOfExSteps, aborter)) {
                    return false;
                }
            }
            if(nextTriple.y != null) {
                if(!this.expand(graph, recursiveClauses, recursivePredicates, nextTriple.y, numberOfExSteps, aborter)) {
                    return false;
                }
            }
            if(nextTriple.z != null) {
                if(!this.expand(graph, recursiveClauses, recursivePredicates, nextTriple.z, numberOfExSteps, aborter)) {
                    return false;
                }
            }
            return true;
        }
        nextTriple = graph.expandArithComp(node, aborter);
        aborter.checkAbortion();
        if (nextTriple != null) {
            if(nextTriple.x != null) {
                if(!this.expand(graph, recursiveClauses, recursivePredicates, nextTriple.x, numberOfExSteps, aborter)) {
                    return false;
                }
            }
            if(nextTriple.y != null) {
                if(!this.expand(graph, recursiveClauses, recursivePredicates, nextTriple.y, numberOfExSteps, aborter)) {
                    return false;
                }
            }
            if(nextTriple.z != null) {
                if(!this.expand(graph, recursiveClauses, recursivePredicates, nextTriple.z, numberOfExSteps, aborter)) {
                    return false;
                }
            }
            return true;
        }

        final GoalElement headElement = currentState.getHeadOfState();
        final List<GoalElement> state = currentState.getState();
        final int stateSize = state.size();
        PrologTerm headTerm = headElement.getTerm();
        if (headTerm.isConjunction()) {
            headTerm = headTerm.conjunctionHead();
        }
        final FunctionSymbol headSymbol = headTerm.createFunctionSymbol();
        if (
            numberOfExSteps >= this.minExSteps
            && !AbstractGraphBuilderHeuristic.isCuttable(
                headElement,
                currentState.getKnowledgeBase(),
                graph,
                recursiveClauses,
                recursivePredicates,
                aborter
            )
        ) {
            if (stateSize > 1 && graph.calculateActiveCuts(state).isEmpty()) {
                // safe PARALLEL
                nextPair = graph.expandParallel(node, 1);
                if (nextPair != null) {
                    if (this.expand(graph, recursiveClauses, recursivePredicates, nextPair.x, numberOfExSteps, aborter))
                    {
                        aborter.checkAbortion();
                        return this.expand(
                            graph,
                            recursiveClauses,
                            recursivePredicates,
                            nextPair.y,
                            numberOfExSteps,
                            aborter);
                    } else {
                        return false;
                    }
                }
            }
            if (
            // labeled goal with recursive clause
            headElement.hasApplicableClause() && recursiveClauses.contains(headElement.getApplicableClause())
            // or unlabeled goal with recursive predicate
                || !headElement.hasApplicableClause()
                && (recursivePredicates.containsKey(headSymbol) || PrologBuiltins.RECURSIVE_BUILTIN_PREDICATES
                    .containsKey(headSymbol)))
            {
                if (!headElement.hasApplicableClause()) {
                    if (
                        graph.expandInstance(
                            node,
                            this.generateIteratorForInstanceCandidates(graph, node, recursivePredicates),
                            this.noGroundLoss,
                            aborter
                        ) != null
                    ) {
                        return true;
                    }
                    aborter.checkAbortion();
                    final Pair<Node<PrologAbstractState>, GeneralizationRule> generalizationStep =
                        this.generalizationStep(graph, node, aborter);
                    if (generalizationStep != null) {
                        if (
                            graph.expandGeneralization(
                                node,
                                generalizationStep.x,
                                generalizationStep.y,
                                this.noGroundLoss,
                                aborter
                            )
                        ) {
                            return
                                this.expand(
                                    graph,
                                    recursiveClauses,
                                    recursivePredicates,
                                    generalizationStep.x,
                                    numberOfExSteps,
                                    aborter
                                );
                        }
                    }
                }
                aborter.checkAbortion();
                if (stateSize > 1) {
                    for (int i = 1; i < stateSize; i++) {
                        if (aborter.isAborted()) {
                            return false;
                        }
                        nextPair = graph.expandParallel(node, i);
                        if (nextPair != null) {
                            if (this.expand(
                                graph,
                                recursiveClauses,
                                recursivePredicates,
                                nextPair.x,
                                numberOfExSteps,
                                aborter))
                            {
                                aborter.checkAbortion();
                                return this.expand(
                                    graph,
                                    recursiveClauses,
                                    recursivePredicates,
                                    nextPair.y,
                                    numberOfExSteps,
                                    aborter);
                            } else {
                                return false;
                            }
                        }
                    }
                } else if (headElement.getTerm().isConjunction()) {
                    nextPair = graph.expandSplit(node, this.getGroundnessAnalysis());
                    if (nextPair != null) {
                        if (this.expand(
                            graph,
                            recursiveClauses,
                            recursivePredicates,
                            nextPair.x,
                            numberOfExSteps,
                            aborter))
                        {
                            aborter.checkAbortion();
                            return this.expand(
                                graph,
                                recursiveClauses,
                                recursivePredicates,
                                nextPair.y,
                                numberOfExSteps,
                                aborter);
                        } else {
                            return false;
                        }
                    }
                }
            }
        }
        nextNode = graph.expandCase(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps + 1, aborter);
        }
        nextNode = graph.expandCall(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps + 1, aborter);
        }
        nextNode = graph.expandNot(node);
        aborter.checkAbortion();
        if (nextNode != null) {
            return this.expand(graph, recursiveClauses, recursivePredicates, nextNode, numberOfExSteps, aborter);
        }
        nextPair = graph.expandEval(node, aborter);
        aborter.checkAbortion();
        if (nextPair != null) {
            if (this.expand(graph, recursiveClauses, recursivePredicates, nextPair.x, numberOfExSteps, aborter)) {
                if (nextPair.y != null) {
                    aborter.checkAbortion();
                    return
                        this.expand(
                            graph,
                            recursiveClauses,
                            recursivePredicates,
                            nextPair.y,
                            numberOfExSteps,
                            aborter
                        );
                }
                return true;
            }
        }
        return false;
        //        throw new IllegalStateException("Expansion of " + node.toString() + " impossible!");
    }

}
