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
public class OldStandardHeuristic implements GraphBuilderHeuristic {

    /**
     * The standard nested depth for generalization.
     */
    public static final int STANDARD_GENERALIZATION_DEPTH = 7;
    /**
     * The standard policy for generalizing all but one or only the
     * last constructor term.
     */
    public static final boolean STANDARD_GENERALIZATION_POSITION_POLICY = true;

    public static final int STANDARD_MAXIMAL_BRANCHING_FACTOR = 3;

    public static final int STANDARD_MIN_NUM_OF_EVAL = 1;

    public static final boolean STANDARD_NO_GROUND_LOSS = false;

    private static final boolean debug = false; // DEBUG STUFF

    //    private int steps = 0; // DEBUG STUFF

    private GroundnessAnalysis analysis;
    private final int generalizationDepth;
    private final boolean generalizeAtFirstOccurence;
    private final int maximalBranchingFactor;
    private final int minimalNumberOfEvaluations;
    private final boolean noGroundLoss;

    // DEBUG STUFF
    private boolean showTime;
    private boolean showTree;

    // END DEBUG STUFF

    public OldStandardHeuristic() {
        this(
            OldStandardHeuristic.STANDARD_MIN_NUM_OF_EVAL,
            OldStandardHeuristic.STANDARD_GENERALIZATION_DEPTH,
            OldStandardHeuristic.STANDARD_GENERALIZATION_POSITION_POLICY,
            OldStandardHeuristic.STANDARD_MAXIMAL_BRANCHING_FACTOR,
            OldStandardHeuristic.STANDARD_NO_GROUND_LOSS);
    }

    public OldStandardHeuristic(final boolean noGroundLoss) {
        this(
            OldStandardHeuristic.STANDARD_MIN_NUM_OF_EVAL,
            OldStandardHeuristic.STANDARD_GENERALIZATION_DEPTH,
            OldStandardHeuristic.STANDARD_GENERALIZATION_POSITION_POLICY,
            OldStandardHeuristic.STANDARD_MAXIMAL_BRANCHING_FACTOR,
            noGroundLoss);
    }

    public OldStandardHeuristic(final int minimalNumberOfEvaluations) {
        this(
            minimalNumberOfEvaluations,
            OldStandardHeuristic.STANDARD_GENERALIZATION_DEPTH,
            OldStandardHeuristic.STANDARD_GENERALIZATION_POSITION_POLICY,
            OldStandardHeuristic.STANDARD_MAXIMAL_BRANCHING_FACTOR,
            OldStandardHeuristic.STANDARD_NO_GROUND_LOSS);
    }

    public OldStandardHeuristic(final int minimalNumberOfEvaluations, final boolean generalizeAtFirstOccurence) {
        this(
            minimalNumberOfEvaluations,
            OldStandardHeuristic.STANDARD_GENERALIZATION_DEPTH,
            generalizeAtFirstOccurence,
            OldStandardHeuristic.STANDARD_MAXIMAL_BRANCHING_FACTOR,
            OldStandardHeuristic.STANDARD_NO_GROUND_LOSS);
    }

    public OldStandardHeuristic(
        final int minimalNumberOfEvaluations,
        final int generalizationDepth,
        final boolean generalizeAtFirstOccurence,
        final int branchingFactor,
        final boolean noGroundLoss)
    {
        if (minimalNumberOfEvaluations < 1) {
            throw new IllegalArgumentException("Minimal number of evaluations must be positive!");
        }
        if (generalizationDepth < 2) {
            throw new IllegalArgumentException("Generalization depth must be bigger than 1!");
        }
        this.minimalNumberOfEvaluations = minimalNumberOfEvaluations;
        this.generalizationDepth = generalizationDepth;
        this.generalizeAtFirstOccurence = generalizeAtFirstOccurence;
        this.analysis = null;
        this.maximalBranchingFactor = branchingFactor;
        this.noGroundLoss = noGroundLoss;
    }

    /**
     * @param program
     * @param aborter
     */
    @Override
    public PrologEvaluationGraph expand(final PrologProblem obl, final Abortion aborter) {
        final PrologEvaluationGraph tree = PrologEvaluationGraph.create(obl);
        final Map<FunctionSymbol, Integer> recursivePredicates = obl.getProgram().createMapOfRecursivePredicates();
        if (aborter.isAborted()) {
            return null;
        }
        this.analysis = this.generateGroundnessAnalysis(tree);
        final Node<PrologAbstractState> node = tree.getRoot();
        if (aborter.isAborted()) {
            return null;
        }
        final long start = System.nanoTime();
        if (!this.expand(tree, recursivePredicates, node, 0, aborter)) {
            return null;
        }
        if (this.showTime) {
            System.err.println((System.nanoTime() - start));
        }
        if (aborter.isAborted()) {
            return null;
        }
        this.analysis = null;
        //        if (this.showTree) {
        //            tree.showNonModal();
        //        }
        return tree;
    }

    public GroundnessAnalysis generateGroundnessAnalysis(final PrologEvaluationGraph tree) {
        return new GroundnessAnalysis() {

            @Override
            public Set<Integer> getGroundPositions(final FunctionSymbol predicate, final Set<Integer> groundPositions) {
                return this.getGroundPositions(
                    predicate,
                    groundPositions,
                    new LinkedHashMap<Pair<FunctionSymbol, Set<Integer>>, Set<Integer>>());
            }

            private void calculateCandidatesFromFacts(
                final Set<PrologClause> facts,
                final Set<Integer> groundPositions,
                final int arity,
                final Set<Integer> candidates)
            {
                for (final PrologClause fact : facts) {
                    final Set<PrologNonAbstractVariable> groundVars = new LinkedHashSet<PrologNonAbstractVariable>();
                    final PrologTerm head = fact.getHead();
                    for (final Integer i : groundPositions) {
                        if (i >= 0 && i < arity) {
                            groundVars.addAll(head.getArgument(i).createSetOfAllNonAbstractVariables());
                        }
                    }
                    for (int i = 0; i < arity; i++) {
                        if (!groundPositions.contains(i)
                            && !groundVars.containsAll(head.getArgument(i).createSetOfAllNonAbstractVariables()))
                        {
                            candidates.remove(i);
                        }
                    }
                }
            }

            private Set<Integer> calculateResultFromRules(
                final Set<PrologClause> rules,
                final Pair<FunctionSymbol, Set<Integer>> key,
                final Map<Pair<FunctionSymbol, Set<Integer>>, Set<Integer>> candidates)
            {
                Set<Integer> toDelete = null;
                start: do {
                    toDelete = new LinkedHashSet<Integer>();
                    for (final PrologClause rule : rules) {
                        final Set<PrologNonAbstractVariable> groundVars =
                            new LinkedHashSet<PrologNonAbstractVariable>();
                        final PrologTerm head = rule.getHead();
                        for (final Integer i : key.y) {
                            groundVars.addAll(head.getArgument(i).createSetOfAllNonAbstractVariables());
                        }
                        for (final PrologTerm t : rule.getBody().createConjunctionListOfPredications()) {
                            final FunctionSymbol p = t.createFunctionSymbol();
                            final Set<Integer> groundPositions = new LinkedHashSet<Integer>();
                            for (int i = 0; i < p.getArity(); i++) {
                                if (groundVars.containsAll(t.getArgument(i).createSetOfAllNonAbstractVariables())) {
                                    groundPositions.add(i);
                                }
                            }
                            final Pair<FunctionSymbol, Set<Integer>> pair =
                                new Pair<FunctionSymbol, Set<Integer>>(p, groundPositions);
                            if (!candidates.containsKey(pair)) {
                                candidates.put(pair, this.getGroundPositions(p, groundPositions, candidates));
                            }
                            for (final Integer i : candidates.get(pair)) {
                                groundVars.addAll(t.getArgument(i).createSetOfAllNonAbstractVariables());
                            }
                        }
                        for (int i = 0; i < key.x.getArity(); i++) {
                            if (!groundVars.containsAll(head.getArgument(i).createSetOfAllNonAbstractVariables())) {
                                toDelete.add(i);
                            }
                        }
                        toDelete.retainAll(candidates.get(key));
                        if (!toDelete.isEmpty()) {
                            candidates.get(key).removeAll(toDelete);
                            continue start;
                        }
                    }
                } while (!toDelete.isEmpty());
                return candidates.get(key);
            }

            private Set<Integer> getGroundPositions(
                final FunctionSymbol predicate,
                final Set<Integer> groundPositions,
                final Map<Pair<FunctionSymbol, Set<Integer>>, Set<Integer>> candidates)
            {
                final Set<PrologClause> facts = new LinkedHashSet<PrologClause>(), rules =
                    new LinkedHashSet<PrologClause>();
                for (final PrologClause clause : tree.getProgram().getClausesForPredicate(predicate)) {
                    if (clause.isFact()) {
                        facts.add(clause);
                    } else {
                        rules.add(clause);
                    }
                }
                final Set<Integer> candidateSet = new LinkedHashSet<Integer>();
                for (int i = 0; i < predicate.getArity(); i++) {
                    candidateSet.add(i);
                }
                this.calculateCandidatesFromFacts(facts, groundPositions, predicate.getArity(), candidateSet);
                final Pair<FunctionSymbol, Set<Integer>> pair =
                    new Pair<FunctionSymbol, Set<Integer>>(predicate, groundPositions);
                candidates.put(pair, candidateSet);
                return this.calculateResultFromRules(rules, pair, candidates);
            }

        };
    }

    //    /**
    //     * @param tree
    //     * @param recursivePredicates
    //     * @param node
    //     * @param numberOfEvaluations
    //     * @param numberOfEvaluations2
    //     */
    //    private void expandSplit(PartEvalTree tree, Set<FunctionSymbol> recursivePredicates, Node<PartEvalTerm> node, int numberOfSplits, int numberOfEvaluations) {
    //        Pair<Node<PartEvalTerm>, Node<PartEvalTerm>> nextPair = tree.expandSplit(node, this.analysis);
    //        if (nextPair != null) {
    //            this.expand(tree, recursivePredicates, nextPair.x, numberOfEvaluations);
    //            if (numberOfSplits > 1) {
    //                this.expandSplit(tree, recursivePredicates, nextPair.y, numberOfSplits - 1, numberOfEvaluations);
    //            } else {
    //                this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations);
    //            }
    //        } else {
    //            int numberOfStateElements = 0,
    //                limit = node.getObject().getState().size();
    //            while (nextPair == null) {
    //                numberOfStateElements++;
    //                if (numberOfStateElements >= limit) {
    //                    throw new IllegalStateException("No PARALLEL possible!");
    //                }
    //                nextPair = tree.expandParallel(node, numberOfStateElements);
    //            }
    //            this.expandSplit(tree, recursivePredicates, nextPair.x, numberOfSplits, numberOfEvaluations);
    //            this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations);
    //        }
    //    }
    //
    //    /**
    //     * @param tree
    //     * @param recursivePredicates
    //     * @param node
    //     * @param length
    //     * @param numberOfEvaluations
    //     */
    //    private void expandParallel(PartEvalTree tree, Set<FunctionSymbol> recursivePredicates, Node<PartEvalTerm> node, int length, int numberOfEvaluations, Iterable<Node<PartEvalTerm>> iterator) {
    //        Pair<Node<PartEvalTerm>, Node<PartEvalTerm>> nextPair = null;
    //        int numberOfStateElements = length - 1,
    //            limit = node.getObject().getState().size();
    //        while (nextPair == null) {
    //            numberOfStateElements++;
    //            if (numberOfStateElements >= limit) {
    //                throw new IllegalStateException("No PARALLEL possible!");
    //            }
    //            nextPair = tree.expandParallel(node, numberOfStateElements);
    //        }
    //        if (numberOfStateElements > length) {
    //            this.expandParallel(tree, recursivePredicates, nextPair.x, length, numberOfEvaluations, iterator);
    //            this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations);
    //        } else {
    //            if (tree.expandInstance(nextPair.x, iterator) == null) {
    //                throw new IllegalStateException("No INSTANCE possible!");
    //            }
    //            this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations);
    //        }
    //    }

    /**
     * @param tree
     * @param node
     * @return
     */
    public Iterable<Node<PrologAbstractState>> generateIteratorForInstanceSearch(
        final PrologEvaluationGraph tree,
        final Node<PrologAbstractState> node,
        final Map<FunctionSymbol, Integer> recursivePredicates)
    {
        final PrologEvaluationGraph t = tree;
        final Queue<Node<PrologAbstractState>> queue = new ArrayDeque<Node<PrologAbstractState>>();
        final Node<PrologAbstractState> n = node;
        final Set<Node<PrologAbstractState>> instanceChildren = tree.getInstanceChildren(node);
        final OldStandardHeuristic heuristic = this;
        final Queue<Node<PrologAbstractState>> toOffer = new ArrayDeque<Node<PrologAbstractState>>();
        if (!tree.getRoot().equals(node)) {
            toOffer.offer(tree.getRoot());
        }
        while (!toOffer.isEmpty()) {
            final Node<PrologAbstractState> toCheck = toOffer.poll();
            if (!node.equals(toCheck)
                && this.instanceCriterion(recursivePredicates, node.getObject(), toCheck.getObject())
                && tree.oneEvalBetweenOrDifferentPath(toCheck, node)
                && !instanceChildren.contains(toCheck))
            {
                queue.offer(toCheck);
            } else {
                for (final Edge<AbstractInferenceRule, PrologAbstractState> edge : tree.getNonInstanceOutEdges(toCheck)) {
                    toOffer.offer(edge.getEndNode());
                }
            }
        }
        return new Iterable<Node<PrologAbstractState>>() {

            @Override
            public Iterator<Node<PrologAbstractState>> iterator() {
                return new Iterator<Node<PrologAbstractState>>() {

                    @Override
                    public boolean hasNext() {
                        return !queue.isEmpty();
                    }

                    @Override
                    public Node<PrologAbstractState> next() {
                        final Node<PrologAbstractState> node = queue.poll();
                        final Queue<Node<PrologAbstractState>> toOffer = new ArrayDeque<Node<PrologAbstractState>>();
                        for (final Edge<AbstractInferenceRule, PrologAbstractState> edge : t.getNonInstanceOutEdges(node)) {
                            toOffer.offer(edge.getEndNode());
                        }
                        while (!toOffer.isEmpty()) {
                            final Node<PrologAbstractState> toCheck = toOffer.poll();
                            if (!n.equals(toCheck)
                                && heuristic.instanceCriterion(recursivePredicates, n.getObject(), toCheck.getObject())
                                && t.oneEvalBetweenOrDifferentPath(toCheck, n)
                                && !instanceChildren.contains(toCheck))
                            {
                                queue.offer(toCheck);
                            } else {
                                for (final Edge<AbstractInferenceRule, PrologAbstractState> edge : t
                                    .getNonInstanceOutEdges(toCheck))
                                {
                                    toOffer.offer(edge.getEndNode());
                                }
                            }
                        }
                        return node;
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }

                };
            }

        };
    }

    @Override
    public void showGraph(final boolean show) {
        this.showTree = show;
    }

    @Override
    public void showTime(final boolean show) {
        this.showTime = show;
    }

    /**
     * @param tree
     * @param recursivePredicates
     * @param node
     * @param aborter
     * @param b
     */
    private boolean expand(
        final PrologEvaluationGraph tree,
        final Map<FunctionSymbol, Integer> recursivePredicates,
        final Node<PrologAbstractState> node,
        final int numberOfEvaluations,
        final Abortion aborter)
    {
        // DEBUG STUFF
        //        this.steps++;
        //        if (steps > 20) {
        //            return;
        //        }
        //        System.err.println(this.steps);
        //        if (this.steps % 50 == 0) {
        //            tree.show();
        //        }
        //        if (node.getNodeNumber() == 11) {
        //            System.err.println("Here!");
        //        }
        //        if (OldStandardHeuristic.debug) {
        //            tree.show();
        //        }
        // END DEBUG STUFF
        final PrologAbstractState pet = node.getObject();
        if (pet.isEmpty()) { // a leaf is a leaf is a leaf
            return true;
        }
        Node<PrologAbstractState> nextNode = tree.expandSuccess(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations + 1, aborter);
        }
        nextNode = tree.expandFailure(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations + 1, aborter);
        }
        nextNode = tree.expandUndefinedError(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations + 1, aborter);
        }
        nextNode = tree.expandVariableError(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations + 1, aborter);
        }
        nextNode = tree.expandCut(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations + 1, aborter);
        }
        nextNode = tree.expandBacktrack(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations + 1, aborter);
        }
        PrologTerm headTerm = node.getObject().getHeadOfState().getTerm();
        while (headTerm.isConjunction()) {
            headTerm = headTerm.conjunctionHead();
        }
        if (recursivePredicates.containsKey(headTerm.createFunctionSymbol())) {
            if (numberOfEvaluations >= this.minimalNumberOfEvaluations) {
                if (
                    tree.expandInstance(
                        node,
                        this.generateIteratorForInstanceSearch(tree, node, recursivePredicates),
                        this.noGroundLoss,
                        aborter
                    ) != null
                ) {
                    return true;
                }
            }
            if (aborter.isAborted()) {
                return false;
            }
            nextNode =
                tree.expandGeneralizationInGraph(node, this.generalizationDepth - 1, this.generalizeAtFirstOccurence);
            if (aborter.isAborted()) {
                return false;
            }
            if (nextNode != null) {
                return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations, aborter);
            }
            final GoalElement e = pet.getHeadOfState();
            final PrologTerm t = e.getTerm();
            final List<GoalElement> checkState = new ArrayList<GoalElement>();
            checkState.add(e);
            final int stateSize = pet.getState().size();
            if (aborter.isAborted()) {
                return false;
            }
            if (stateSize > 1 && tree.calculateActiveCuts(checkState).isEmpty()) { // safe PARALLEL
                final Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> nextPair = tree.expandParallel(node, 1);
                if (nextPair == null) {
                    throw new IllegalStateException("No PARALLEL possible!");
                }
                if (aborter.isAborted()) {
                    return false;
                }
                this.expand(tree, recursivePredicates, nextPair.x, numberOfEvaluations, aborter);
                if (aborter.isAborted()) {
                    return false;
                }
                return this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations, aborter);
            } else if (stateSize == 1
                && t.isConjunction()
                && recursivePredicates.containsKey(t.getArgument(0).createFunctionSymbol()))
            {
                final Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> nextPair = tree.expandSplit(node, this.analysis);
                if (nextPair == null) {
                    throw new IllegalStateException("No SPLIT possible!");
                }
                if (aborter.isAborted()) {
                    return false;
                }
                this.expand(tree, recursivePredicates, nextPair.x, numberOfEvaluations, aborter);
                if (aborter.isAborted()) {
                    return false;
                }
                return this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations, aborter);
            }
            final List<PrologAbstractState> singlePreds = new ArrayList<PrologAbstractState>();
            if (!e.hasApplicableClause()) {
                final KnowledgeBase kb = pet.getKnowledgeBase();
                for (final PrologTerm c : t.createConjunctionListOfPredications()) {
                    if (c.isVariable() || c.isCut()) {
                        singlePreds.add(null);
                    } else {
                        singlePreds.add(PrologAbstractState.createFromTerm(c, kb));
                    }
                }
            }
            if (aborter.isAborted()) {
                return false;
            }
            for (final Node<PrologAbstractState> toCheck : this.generateIteratorForInstanceSearch(
                tree,
                node,
                recursivePredicates))
            {
                if (!tree.contains(toCheck)) {
                    continue;
                }
                Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> nextPair = null;
                if (aborter.isAborted()) {
                    return false;
                }
                final int length =
                    PrologAbstractState.calculateMaximalStateLengthForInstance(
                        pet,
                        toCheck.getObject(),
                        this.noGroundLoss,
                        aborter
                    );
                if (length > 0 && length < stateSize) {
//                    this.expandParallel(
//                        tree,
//                        recursivePredicates,
//                        node,
//                        length,
//                        numberOfEvaluations,
//                        this.generateIteratorForInstanceSearch(tree, node)
//                    );
                    if (aborter.isAborted()) {
                        return false;
                    }
                    nextPair = tree.expandParallel(node, length);
                    if (nextPair != null) {
                        if (aborter.isAborted()) {
                            return false;
                        }
                        this.expand(tree, recursivePredicates, nextPair.x, numberOfEvaluations, aborter);
                        if (aborter.isAborted()) {
                            return false;
                        }
                        return this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations, aborter);
                    }
                }
                for (int i = 0; i < singlePreds.size(); i++) {
                    final PrologAbstractState tPet = singlePreds.get(i);
                    if (aborter.isAborted()) {
                        return false;
                    }
                    if (
                        tPet != null
                        && PrologAbstractState.calculateInstanceMatcher(
                            tPet,
                            toCheck.getObject(),
                            this.noGroundLoss,
                            aborter
                        ) != null
                        && recursivePredicates.containsKey(tPet.getHeadOfState().getTerm().createFunctionSymbol())
                    ) {
//                        this.expandSplit(tree, recursivePredicates, node, i + 1, numberOfEvaluations);
                        if (aborter.isAborted()) {
                            return false;
                        }
                        nextPair = tree.expandSplit(node, this.analysis);
                        if (nextPair != null) {
                            if (aborter.isAborted()) {
                                return false;
                            }
                            this.expand(tree, recursivePredicates, nextPair.x, numberOfEvaluations, aborter);
                            if (aborter.isAborted()) {
                                return false;
                            }
                            return this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations, aborter);
                        }
                    }
                }
            }
        }
        nextNode = tree.expandCase(node);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations, aborter);
        }
        nextNode = tree.expandCall(node);
        if (nextNode != null) {
            return this.expand(tree, recursivePredicates, nextNode, numberOfEvaluations, aborter);
        }
        final Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> nextPair = tree.expandEval(node, aborter);
        if (aborter.isAborted()) {
            return false;
        }
        if (nextPair != null) {
            if (this.expand(tree, recursivePredicates, nextPair.x, numberOfEvaluations + 1, aborter)) {
                if (nextPair.y != null) {
                    if (aborter.isAborted()) {
                        return false;
                    }
                    return this.expand(tree, recursivePredicates, nextPair.y, numberOfEvaluations + 1, aborter);
                }
                return true;
            }
        }
        return false;
        //        throw new IllegalStateException("Expansion of " + node.toString() + " impossible!");
    }

    private boolean instanceCriterion(
        final Map<FunctionSymbol, Integer> recursivePredicates,
        final PrologAbstractState child,
        final PrologAbstractState parent)
    {
        PrologTerm term = child.getHeadOfState().getTerm();
        if (term == null) {
            return false;
        }
        if (term.isConjunction()) {
            term = term.conjunctionHead();
        }
        final Integer num = recursivePredicates.get(term.createFunctionSymbol());
        if (num == null) {
            return false;
        }
        if (num > this.maximalBranchingFactor) {
            return true;
        }
        // alternative/additional ideas:
        // * always allow instances to finite trees
        // * look at substitution to determine if there are function symbols
        //   not occurring in the heads of the recursive predicate's clauses

        final Set<PrologVariable> childVars = child.createSetOfAllVariablesInState();
        final Set<PrologVariable> parentVars = parent.createSetOfAllVariablesInState();
        final int numberOfChildVars = childVars.size();
        final int numberOfParentVars = parentVars.size();
        if (numberOfChildVars > numberOfParentVars) {
            return true;
        } else if (numberOfChildVars == numberOfParentVars) {
            int numberOfAbstractChildVars = 0, numberOfAbstractParentVars = 0;
            for (final PrologVariable var : childVars) {
                if (var.isAbstractVariable()) {
                    numberOfAbstractChildVars++;
                }
            }
            for (final PrologVariable var : parentVars) {
                if (var.isAbstractVariable()) {
                    numberOfAbstractParentVars++;
                }
            }
            return numberOfAbstractChildVars >= numberOfAbstractParentVars;
        } else {
            return false;
        }
    }

}
