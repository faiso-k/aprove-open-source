package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * A PrologGraphProcessor builds a termination graph for a
 * given PrologProgram which can then be used to construct
 * various programs in other languages whose termination or
 * upper complexity bound implies the same for the original
 * PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class PrologGraphProcessor extends PrologProblemProcessor {

    /**
     * Show graph before computing a new obligation?
     */
    private static boolean TRANSFORMATION_DEBUG = false;

    /**
     * @param graph
     * @param aborter
     * @return
     */
    public static Set<List<Node<PrologAbstractState>>> calculateAllClausePaths(
        PrologEvaluationGraph graph,
        NodeSets sets,
        Abortion aborter
    ) {
        Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        for (Node<PrologAbstractState> node : sets.getInstanceChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            res.addAll(PrologGraphProcessor.calculateAllClausePathsFromNode(
                graph,
                node,
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        for (Node<PrologAbstractState> node : sets.getGeneralizationChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            res.addAll(PrologGraphProcessor.calculateAllClausePathsFromNode(
                graph,
                node,
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        for (Node<PrologAbstractState> node : sets.getLeftSplitChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            res.addAll(PrologGraphProcessor.calculateAllClausePathsFromNode(
                graph,
                node,
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        if (aborter.isAborted()) {
            return new LinkedHashSet<List<Node<PrologAbstractState>>>();
        }
        return res;
    }

    /**
     * @param graph
     * @param node
     * @param currentPath
     * @param sets
     * @param aborter
     * @return
     */
    public static Set<List<Node<PrologAbstractState>>> calculateAllClausePathsFromNode(
        PrologEvaluationGraph graph,
        Node<PrologAbstractState> node,
        List<Node<PrologAbstractState>> currentPath,
        NodeSets sets,
        Abortion aborter
    ) {
        if (aborter.isAborted()) {
            return new LinkedHashSet<List<Node<PrologAbstractState>>>();
        }
        List<Node<PrologAbstractState>> nextPath = new ArrayList<Node<PrologAbstractState>>(currentPath);
        nextPath.add(node);
        Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        if (nextPath.size() > 1 && sets.getSuccessNodes().contains(node)) {
            res.add(nextPath);
            nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
        }
        if (nextPath.size() > 1
            && (sets.getInstanceChildren().contains(node)
                || sets.getInstanceNodes().contains(node)
                || sets.getGeneralizationChildren().contains(node) || sets.getGeneralizationNodes().contains(node))
            && !sets.getLeftSplitChildren().contains(node))
        {
            res.add(nextPath);
        } else if (!sets.getInstanceNodes().contains(node)
            && !sets.getGeneralizationNodes().contains(node)
            && !(nextPath.size() > 1 && (sets.getInstanceChildren().contains(node)
                || sets.getGeneralizationChildren().contains(node) || sets.getLeftSplitChildren().contains(node))))
        {
            for (Node<PrologAbstractState> child : graph.getOut(node)) {
                if (aborter.isAborted()) {
                    return new LinkedHashSet<List<Node<PrologAbstractState>>>();
                }
                res.addAll(PrologGraphProcessor.calculateAllClausePathsFromNode(graph, child, nextPath, sets, aborter));
                nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            }
        }
        return res;
    }

    /**
     * @param graph
     * @param aborter
     * @return
     */
    public static Set<List<Node<PrologAbstractState>>> calculateAllTriplePaths(
        PrologEvaluationGraph graph,
        NodeSets sets,
        Abortion aborter
    ) {
        Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        for (Node<PrologAbstractState> node : sets.getInstanceChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            if (!graph.isRoot(node)) {
                res.addAll(PrologGraphProcessor.calculateAllTriplePathsFromNode(
                    graph,
                    node,
                    new ArrayList<Node<PrologAbstractState>>(),
                    sets,
                    aborter));
            }
        }
        for (Node<PrologAbstractState> node : sets.getGeneralizationChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            if (!graph.isRoot(node)) {
                res.addAll(PrologGraphProcessor.calculateAllTriplePathsFromNode(
                    graph,
                    node,
                    new ArrayList<Node<PrologAbstractState>>(),
                    sets,
                    aborter));
            }
        }
        if (!graph.getRoot().getObject().isEmpty()) {
            res.addAll(PrologGraphProcessor.calculateAllTriplePathsFromNode(
                graph,
                graph.getRoot(),
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        if (aborter.isAborted()) {
            return new LinkedHashSet<List<Node<PrologAbstractState>>>();
        }
        return res;
    }

    /**
     * @param graph
     * @param node
     * @param currentPath
     * @param sets
     * @param aborter
     * @return
     */
    public static Set<List<Node<PrologAbstractState>>> calculateAllTriplePathsFromNode(
        PrologEvaluationGraph graph,
        Node<PrologAbstractState> node,
        List<Node<PrologAbstractState>> currentPath,
        NodeSets sets,
        Abortion aborter
    ) {
        if (aborter.isAborted()) {
            return new LinkedHashSet<List<Node<PrologAbstractState>>>();
        }
        List<Node<PrologAbstractState>> nextPath = new ArrayList<Node<PrologAbstractState>>(currentPath);
        nextPath.add(node);
        Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        if (nextPath.size() > 1
            && (sets.getInstanceChildren().contains(node)
                || sets.getInstanceNodes().contains(node)
                || sets.getGeneralizationChildren().contains(node) || sets.getGeneralizationNodes().contains(node)))
        {
            res.add(nextPath);
        } else if (!sets.getInstanceNodes().contains(node)
            && !sets.getGeneralizationNodes().contains(node)
            && !(nextPath.size() > 1 && (sets.getInstanceChildren().contains(node) || sets
                .getGeneralizationChildren()
                .contains(node))))
        {
            for (Node<PrologAbstractState> child : graph.getOut(node)) {
                if (aborter.isAborted()) {
                    return new LinkedHashSet<List<Node<PrologAbstractState>>>();
                }
                res.addAll(PrologGraphProcessor.calculateAllTriplePathsFromNode(graph, child, nextPath, sets, aborter));
                nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            }
        }
        return res;
    }

    /**
     * @param rule
     * @return
     */
    public static PrologSubstitution getAnswerSubstitution(AbstractInferenceRule rule) { // TODO add remaining rules
        switch (rule.rule()) {
        case EVAL:
            return ((EvalRule) rule).getSubstitution().deepCopy();
        case ONLY_EVAL:
            return ((OnlyEvalRule) rule).getSubstitution().deepCopy();
        case SPLIT:
            SplitCase sCase = ((SplitRule) rule).getSplitCase();
            if (sCase == null) {
                return new PrologSubstitution();
            }
            return sCase.getReplacements().deepCopy();
        case UNIFY_CASE:
            return ((UnifyCaseRule) rule).getSubstitution().deepCopy();
        case UNIFY_SUCCESS:
            return ((UnifySuccessRule) rule).getSubstitution().deepCopy();
        default:
            return new PrologSubstitution();
        }
    }

    /**
     * @param rule
     * @return
     */
    public static PrologSubstitution getBacktrackSubstitution(AbstractInferenceRule rule) { // TODO add remaining rules
        switch (rule.rule()) {
        case EVAL:
            return ((EvalRule) rule).getGroundSubstitution().deepCopy();
        case ONLY_EVAL:
            return ((OnlyEvalRule) rule).getGroundSubstitution().deepCopy();
        case UNIFY_CASE:
            return ((UnifyCaseRule) rule).getGroundSubstitution().deepCopy();
        case UNIFY_SUCCESS:
            return ((UnifySuccessRule) rule).getGroundSubstitution().deepCopy();
        default:
            return new PrologSubstitution();
        }
    }

    /**
     * @param graph
     * @param n1
     * @param n2
     * @return
     */
    public static int getChange(
        PrologEvaluationGraph graph,
        Node<PrologAbstractState> n1,
        Node<PrologAbstractState> n2
    ) {
        if (graph.isParallelNode(n1) && graph.getLastChild(n1).equals(n2)) {
            return graph.getFirstChild(n1).getObject().getState().size();
        }
        if (graph.isCutNode(n1)) {
            return n1.getObject().getState().size() - n2.getObject().getState().size();
        }
        if (graph.isCaseNode(n1)) {
            PrologTerm t = n1.getObject().getHeadOfState().getTerm();
            if (t.isConjunction()) {
                t = t.conjunctionHead();
            }
            return graph.slice(t).size();
        }
        if (PrologGraphProcessor.isBacktracking(graph, n1)
            || graph.isCallNode(n1)
            || graph.isDisjunctionNode(n1)
            || graph.isIfThenNode(n1)
            || graph.isRepeatNode(n1)
            || (graph.getLastChild(n1).equals(n2) && (graph.isBacktrackSecond(n1) || graph.isVarCaseNode(n1))))
        {
            return 1;
        }
        if (graph.isIfThenElseNode(n1) || graph.isNotNode(n1)) {
            return 2;
        }
        return 0;
    }

    /**
     * @param graph
     * @param n1
     * @param n2
     * @param skip
     * @return
     */
    public static int getReduce(
        PrologEvaluationGraph graph,
        Node<PrologAbstractState> n1,
        Node<PrologAbstractState> n2,
        int skip
    ) {
        final int change = PrologGraphProcessor.getChange(graph, n1, n2);
        if (change > skip) {
            return 0;
        }
        return skip - change;
    }

    /**
     * @param graph
     * @param node
     * @param clause
     * @param nodeLabels
     * @return
     */
    public static PrologTerm getRenamedPrologTermForNode(
        PrologEvaluationGraph graph,
        Node<PrologAbstractState> node,
        boolean clause,
        Map<Integer, String> nodeLabels
    ) {
        if (graph.isSuccessNode(node)) {
            return PrologTerms.createTrue();
        } else if (graph.isInstanceNode(node)) {
            Node<PrologAbstractState> child = graph.getFirstChild(node);
            PrologTerm res = PrologGraphProcessor.getRenamedPrologTermForNode(graph, child, clause, nodeLabels);
            InstanceRule step = (InstanceRule) graph.getEdgeObject(node, child);
            PrologSubstitution mu = step.getMatcher();
            return res.applySubstitution(mu);
        } else if (graph.isGeneralizationNode(node)) {
            Node<PrologAbstractState> child = graph.getFirstChild(node);
            PrologTerm res = PrologGraphProcessor.getRenamedPrologTermForNode(graph, child, clause, nodeLabels);
            GeneralizationRule step = (GeneralizationRule) graph.getEdgeObject(node, child);
            PrologSubstitution mu = step.getGeneralizationAsSubstitution();
            return res.applySubstitution(mu);
        } else {
            PrologAbstractState pet = node.getObject();
            if (!pet.isEmpty()) {
                PrologTerm term = pet.getHeadOfState().getTerm();
                final int nodeNumber = node.getNodeNumber();
                if (!nodeLabels.containsKey(nodeNumber)) {
                    final int size = nodeLabels.size();
                    String nodeLabel;
                    if (size > 25) {
                        nodeLabel = "N" + (size - 25);
                    } else {
                        nodeLabel = "" + (char) ('A' + size);
                    }
                    nodeLabels.put(nodeNumber, nodeLabel);
                }
                return new PrologTerm(graph.getFNG().getFreshName(
                    (term.isConjunction() ? (clause ? "q" : "p") : term.getName())
                        + (clause ? "c" : "")
                        + nodeLabels.get(nodeNumber),
                    true), PrologGraphProcessor.getVariableListForRename(node));
            } else {
                throw new IllegalArgumentException("Cannot encode empty state!");
            }
        }
    }

    /**
     * @param graph The graph that the given path exists in. Must not be null.
     * @param path A sequence of nodes where each node has an edge to the next one in the list. Must not be null.
     * @param skip Should be set to 0 on first call. Used internally for recursive calls.
     * @param aborter Some Abortion. Used to check if we have exceeded the timeout. Must not be null.
     * @return The concatenation of all substitutions along this path.
     * @throws AbortionException If we are aborted during this call.
     */
    public static PrologSubstitution getSubstitutionForPath(
        PrologEvaluationGraph graph,
        List<Node<PrologAbstractState>> path,
        int skip,
        Abortion aborter
    ) throws AbortionException {
        aborter.checkAbortion();
        if (path.size() > 1) { // for paths of size 1 we return id
            // restPath = n_1...n_{j-1}
            List<Node<PrologAbstractState>> restPath = new ArrayList<Node<PrologAbstractState>>();
            for (int i = 0; i < path.size() - 1; i++) {
                restPath.add(path.get(i));
            }
            // node = n_{j-1}, lastNode = n_j
            Node<PrologAbstractState> node = path.get(path.size() - 2);
            Node<PrologAbstractState> lastNode = path.get(path.size() - 1);
            // case for answer substitution
            if ((graph.isSplitNode(node) && !((SplitRule) graph.getEdgeObject(node, lastNode)).isFirstSplit())
                || (graph.isEqualsCaseNode(node) && graph.getFirstChild(node).equals(lastNode))
                || (skip == 0 && (graph.isUnifySuccessNode(node) || graph.isOnlyEvalNode(node) || (graph.getFirstChild(
                    node).equals(lastNode) && (graph.isUnifyCaseNode(node) || graph.isEvalNode(node))))))
            {
                return PrologGraphProcessor.assertingAppend(
                    PrologGraphProcessor.getSubstitutionForPath(graph, restPath, skip, aborter),
                    PrologGraphProcessor.getAnswerSubstitution(graph.getEdgeObject(node, lastNode)),
                    node.getObject().getHeadOfState().getTerm().createSetOfAllVariables(),
                    path);
            }
            // case for backtrack substitution
            if (skip > 0
                && (graph.isOnlyEvalNode(node) || graph.isUnifySuccessNode(node) || (graph.getFirstChild(node).equals(
                    lastNode) && (graph.isEvalNode(node) || graph.isUnifyCaseNode(node)))))
            {
                return PrologGraphProcessor.assertingAppend(
                    PrologGraphProcessor.getSubstitutionForPath(graph, restPath, skip, aborter),
                    PrologGraphProcessor.getBacktrackSubstitution(graph.getEdgeObject(node, lastNode)),
                    node.getObject().getHeadOfState().getTerm().createSetOfAllVariables(),
                    path);
            }
            // case for backtrack substitution plus backtracking
            if (graph.isNoUnifyFailNode(node)
                || (graph.getLastChild(node).equals(lastNode) && (graph.isNoUnifyCaseNode(node) || graph
                    .isUnequalsCaseNode(node))))
            {
                return PrologGraphProcessor.assertingAppend(
                    PrologGraphProcessor.getSubstitutionForPath(graph, restPath, skip + 1, aborter),
                    PrologGraphProcessor.getBacktrackSubstitution(graph.getEdgeObject(node, lastNode)),
                    node.getObject().getHeadOfState().getTerm().createSetOfAllVariables(),
                    path);
            }
            // case for VAR_CASE
            // TODO
            // case for backtracking or cutting
            if (PrologGraphProcessor.isBacktracking(graph, node)
                || (graph.getLastChild(node).equals(lastNode) && (graph.isBacktrackSecond(node) || graph
                    .isVarCaseNode(node))) || (skip > 0 && graph.isCutNode(node)))
            {
                return PrologGraphProcessor.getSubstitutionForPath(
                    graph,
                    restPath,
                    skip + PrologGraphProcessor.getChange(graph, node, lastNode),
                    aborter);
            }
            // case for introducing
            if (graph.isIntroducing(node)) {
                return PrologGraphProcessor.getSubstitutionForPath(
                    graph,
                    restPath,
                    PrologGraphProcessor.getReduce(graph, node, lastNode, skip),
                    aborter);
            }
            // for all other operations, just recurse!
            return PrologGraphProcessor.getSubstitutionForPath(graph, restPath, skip, aborter);
        } else {
            // return id
            return new PrologSubstitution();
        }
    }

    /**
     * @param graph
     * @param node
     * @return
     */
    public static boolean isBacktracking(PrologEvaluationGraph graph, Node<PrologAbstractState> node) {
        return
            graph.isBacktrackNode(node)
            || graph.isFailureNode(node)
            || graph.isSuccessNode(node)
            || graph.isUnifyFailNode(node)
            || graph.isAtomicFailNode(node)
            || graph.isCompoundFailNode(node)
            || graph.isEqualsFailNode(node)
            || graph.isFailNode(node)
            || graph.isNonvarFailNode(node)
            || graph.isUnequalsFailNode(node)
            || graph.isVarFailNode(node);
    }

    /**
     * @param relevant
     * @param path
     *
     */
    private static PrologSubstitution assertingAppend(
        PrologSubstitution sub1,
        PrologSubstitution sub2,
        Set<PrologVariable> relevant,
        List<Node<PrologAbstractState>> path
    ) {
        if (sub1 == null || sub2 == null) {
            return null;
        }
        if (aprove.Globals.useAssertions) {
            LinkedHashSet<PrologVariable> domain = new LinkedHashSet<PrologVariable>(sub1.keySet());
            domain.retainAll(sub2.keySet());
            domain.retainAll(relevant);
            assert (domain.isEmpty());
        }
        return sub1.append(sub2);
    }

    /**
     * @param node
     * @return
     */
    private static List<PrologTerm> getVariableListForRename(Node<PrologAbstractState> node) {
        List<PrologTerm> res = new ArrayList<PrologTerm>();
        PrologAbstractState pet = node.getObject();
        for (GoalElement element : pet.getState()) {
            if (!element.isQuestionMark()) {
                res.addAll(element.getTerm().createSetOfAllVariables());
            }
        }
        return res;
    }

    /**
     * Object containing all options.
     */
    protected final PrologOptions options;

    /**
     * @param ops
     */
    public PrologGraphProcessor(PrologOptions ops) {
        this.options = ops;
    }

    /**
     * @return
     */
    protected abstract Logger getLogger();

    /**
     * @param graph
     * @param aborter
     * @return
     */
    protected abstract Result processGraph(PrologEvaluationGraph graph, Abortion aborter) throws AbortionException;

    @Override
    protected Result processPrologProblem(PrologProblem pp, Abortion aborter) throws AbortionException {
        final Logger log = this.getLogger();
        long time = 0;
        if (log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        final GraphBuilderHeuristic petHeuristic =
            this.options.isComplexityHeuristic() ? new ComplexityHeuristic(
                this.options.getMinExSteps(),
                this.options.getGeneralizationDepth(),
                this.options.getGeneralizationPosition(),
                this.options.getMaxBranchingFactor(),
                this.options.isNoGroundLoss()) : new TerminationHeuristic(
                this.options.getMinExSteps(),
                this.options.getGeneralizationDepth(),
                this.options.getGeneralizationPosition(),
                this.options.getMaxBranchingFactor(),
                this.options.isNoGroundLoss());
        petHeuristic.showGraph(this.options.isShowTree());
        final PrologEvaluationGraph graph = petHeuristic.expand(pp.setSMT(this.options.getSmt()), aborter);
        if (log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            log.log(Level.FINE, "Constructing Termination Graph: {0}ms\n", time / 1000000);
        }
        if (graph == null) {
            System.out.println("Graph construction failed");
            return ResultFactory.aborted("graph construction failed");
        }
        return this.processGraph(graph, aborter);
    }

}
