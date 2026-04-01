package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.*;
import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author cryingshadow, unknown
 */
public abstract class AbstractGraphBuilderHeuristic implements GraphBuilderHeuristic {

    /**
     * Flag to indicate whether chains of INSTANCE edges are allowed.
     */
    private static final boolean NO_INSTANCE_CHAINS = true;

    /**
     * Groundness analysis function.
     */
    private GroundnessAnalysis analysis;

    private final int generalizationDepth;

    private final int generalizationPosition;

    /**
     * The maximal branching factor up to which we allow nodes to be excluded from instance candidates.
     */
    private final int maxBranchingFactor;

    /**
     * Debug stuff.
     */
    private boolean showTime;

    /**
     * Debug stuff.
     */
    private boolean showTree;

    public AbstractGraphBuilderHeuristic(int genDepth, int genPos, int maxBFactor) {
        this.generalizationDepth = genDepth;
        this.generalizationPosition = genPos;
        this.maxBranchingFactor = maxBFactor;
        this.analysis = null;
    }

    /**
     * @param graph
     * @return
     */
    public static GroundnessAnalysis generateGroundnessAnalysis(final PrologEvaluationGraph graph) {
        return new GroundnessAnalysis() {

            @Override
            public Set<Integer> getGroundPositions(FunctionSymbol predicate, Set<Integer> groundPositions) {
                return this.getGroundPositions(
                    predicate,
                    groundPositions,
                    new LinkedHashMap<Pair<FunctionSymbol, Set<Integer>>, Set<Integer>>());
            }

            /**
             * @param facts
             * @param groundPositions
             * @param arity
             * @param candidates
             */
            private void calculateCandidatesFromFacts(
                Set<PrologClause> facts,
                Set<Integer> groundPositions,
                int arity,
                Set<Integer> candidates
            ) {
                for (PrologClause fact : facts) {
                    Set<PrologNonAbstractVariable> groundVars = new LinkedHashSet<PrologNonAbstractVariable>();
                    PrologTerm head = fact.getHead();
                    for (Integer i : groundPositions) {
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

            /**
             * @param rules
             * @param key
             * @param candidates
             * @return
             */
            private Set<Integer> calculateResultFromRules(
                Set<PrologClause> rules,
                Pair<FunctionSymbol, Set<Integer>> key,
                Map<Pair<FunctionSymbol, Set<Integer>>, Set<Integer>> candidates
            ) {
                Set<Integer> toDelete = null;
                start: do {
                    toDelete = new LinkedHashSet<Integer>();
                    for (PrologClause rule : rules) {
                        Set<PrologNonAbstractVariable> groundVars =
                            new LinkedHashSet<PrologNonAbstractVariable>();
                        PrologTerm head = rule.getHead();
                        for (Integer i : key.y) {
                            groundVars.addAll(head.getArgument(i).createSetOfAllNonAbstractVariables());
                        }
                        for (PrologTerm t : rule.getBody().createConjunctionListOfPredications()) {
                            FunctionSymbol p = t.createFunctionSymbol();
                            Set<Integer> groundPositions = new LinkedHashSet<Integer>();
                            for (int i = 0; i < p.getArity(); i++) {
                                if (groundVars.containsAll(t.getArgument(i).createSetOfAllNonAbstractVariables())) {
                                    groundPositions.add(i);
                                }
                            }
                            Pair<FunctionSymbol, Set<Integer>> pair =
                                new Pair<FunctionSymbol, Set<Integer>>(p, groundPositions);
                            if (!candidates.containsKey(pair)) {
                                candidates.put(pair, this.getGroundPositions(p, groundPositions, candidates));
                            }
                            for (Integer i : candidates.get(pair)) {
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

            /**
             * @param predicate
             * @param groundPositions
             * @param candidates
             * @return
             */
            private Set<Integer> getGroundPositions(
                FunctionSymbol predicate,
                Set<Integer> groundPositions,
                Map<Pair<FunctionSymbol, Set<Integer>>, Set<Integer>> candidates
            ) {
                Set<PrologClause> facts = new LinkedHashSet<PrologClause>();
                Set<PrologClause> rules = new LinkedHashSet<PrologClause>();
                for (PrologClause clause : graph.getProgram().getClausesForPredicate(predicate)) {
                    if (clause.isFact()) {
                        facts.add(clause);
                    } else {
                        rules.add(clause);
                    }
                }
                Set<Integer> candidateSet = new LinkedHashSet<Integer>();
                for (int i = 0; i < predicate.getArity(); i++) {
                    candidateSet.add(i);
                }
                this.calculateCandidatesFromFacts(facts, groundPositions, predicate.getArity(), candidateSet);
                Pair<FunctionSymbol, Set<Integer>> pair =
                    new Pair<FunctionSymbol, Set<Integer>>(predicate, groundPositions);
                candidates.put(pair, candidateSet);
                return this.calculateResultFromRules(rules, pair, candidates);
            }

        };
    }

    /**
     * Tests whether the specified StateElement is labeled with a recursive clause.
     * @param headElement The element to test.
     * @param recursiveClauses The recursive clauses.
     * @return True is the specified StateElement is labeled with a recursive clause.
     */
    public static boolean isLabeledGoalWithRecursiveClause(
        GoalElement headElement,
        Set<Integer> recursiveClauses
    ) {
        return headElement.hasApplicableClause() && recursiveClauses.contains(headElement.getApplicableClause());
    }

    /**
     * Tests whether the specified StateElement is unlabeled, but its first symbol is a recursive predicate.
     * @param headElement The element to test.
     * @param headSymbol The first symbol.
     * @param recursivePredicates The recursive predicates.
     * @return True if the specified StateElement is unlabeled, but its first symbol is a recursive predicate.
     */
    public static boolean isUnlabeledGoalWithRecursivePredicate(
        GoalElement headElement,
        FunctionSymbol headSymbol,
        Map<FunctionSymbol, Integer> recursivePredicates
    ) {
        return !headElement.hasApplicableClause()
            && (recursivePredicates.containsKey(headSymbol) || PrologBuiltins.RECURSIVE_BUILTIN_PREDICATES
                .containsKey(headSymbol));
    }

    protected static boolean isCuttable(
        GoalElement headElement,
        KnowledgeBase kb,
        PrologEvaluationGraph graph,
        Set<Integer> recursiveClauses,
        Map<FunctionSymbol, Integer> recursivePredicates,
        Abortion aborter
    ) {
        if (headElement.isQuestionMark()) {
            return false;
        }
        if (headElement.hasApplicableClause()) {
            Pair<PrologTerm, KnowledgeBase> pair =
                AbstractGraphBuilderHeuristic.applyOnlyEval(headElement, kb, graph, aborter);
            if (pair == null) {
                return false;
            }
            return
                AbstractGraphBuilderHeuristic.isCuttable(
                    pair.x,
                    pair.y,
                    graph,
                    recursiveClauses,
                    recursivePredicates,
                    aborter
                );
        } else {
            return
                AbstractGraphBuilderHeuristic.isCuttable(
                    headElement.getTerm(),
                    kb,
                    graph,
                    recursiveClauses,
                    recursivePredicates,
                    aborter
                );
        }
    }

    private static Pair<PrologTerm, KnowledgeBase> applyOnlyEval(
        GoalElement headElement,
        KnowledgeBase kb,
        PrologEvaluationGraph graph,
        Abortion aborter
    ) {
        //TODO consider UNIFY?
        EvalResults res = graph.computeEvalResults(headElement, kb, true, aborter);
        if (res == null) {
            return null;
        }
        return new Pair<PrologTerm, KnowledgeBase>(res.getBody(), res.getEvalBase());
    }

    private static boolean isBacktrackApplicable(
        GoalElement stateElement,
        KnowledgeBase kb,
        PrologEvaluationGraph graph
    ) {
        PrologTerm completeTerm = stateElement.getTerm();
        PrologTerm t = completeTerm;
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        PrologClause clause = graph.getFreshlyRenamedClause(stateElement.getApplicableClause());
        PrologTerm h = clause.getHead();
        PrologSubstitution sigma = graph.calculateMGUwithOnlyFreshVariables(t, h);
        return kb.computePossibleClash(sigma) != null;
    }

    private static boolean isCuttable(
        PrologTerm term,
        KnowledgeBase kb,
        PrologEvaluationGraph graph,
        Set<Integer> recursiveClauses,
        Map<FunctionSymbol, Integer> recursivePredicates,
        Abortion aborter
    ) {
        List<PrologTerm> conjuncts = term.createConjunctionListOfPredications();
        for (int i = 0; i < conjuncts.size(); i++) {
            PrologTerm t = conjuncts.get(i);
            FunctionSymbol symbol = t.createFunctionSymbol();
            if (t.isCut()) {
                return true;
            } else if (!PrologBuiltins.BUILTIN_PREDICATES.contains(symbol)) {
                List<Integer> slice = graph.slice(t);
                if (slice.isEmpty()) {
                    return true;
                }
                if (recursivePredicates.containsKey(symbol)) {
                    boolean fact = false;
                    for (int j = 0; j < slice.size(); j++) {
                        int clause = slice.get(j);
                        if (
                            graph.getProgram().getClause(clause).isFact()
                            && AbstractGraphBuilderHeuristic.applyOnlyEval(
                                new GoalElement(t, 1, clause),
                                kb,
                                graph,
                                aborter
                            ) != null
                        ) {
                            fact = true;
                            break;
                        }
                        if (!AbstractGraphBuilderHeuristic.isBacktrackApplicable(
                            new GoalElement(t, 1, clause),
                            kb,
                            graph))
                        {
                            return false;
                        }
                    }
                    if (!fact) {
                        return false;
                    }
                }
            } else {
                if (!symbol.equals(PrologBuiltin.REPEAT_PREDICATE)) {
                    return false;
                }
            }
        }
        return false;
    }

    @Override
    public PrologEvaluationGraph expand(PrologProblem obl, Abortion aborter) throws AbortionException {
        PrologEvaluationGraph graph = PrologEvaluationGraph.create(obl);
        PrologProgram program = obl.getProgram();
        Map<FunctionSymbol, Integer> recursivePredicates = program.createMapOfRecursivePredicates();
        Set<Integer> recursiveClauses = program.createSetOfRecursiveClauseNumbers(recursivePredicates);
        aborter.checkAbortion();
        this.analysis = AbstractGraphBuilderHeuristic.generateGroundnessAnalysis(graph);
        Node<PrologAbstractState> node = graph.getRoot();
        aborter.checkAbortion();
        long start = System.nanoTime();
        if (!this.expand(graph, recursiveClauses, recursivePredicates, node, 0, aborter)) {
            //            if (this.showTree) {
            //                graph.showNonModal();
            //            }
            return null;
        }
        if (this.showTime) {
            System.err.println((System.nanoTime() - start));
        }
        aborter.checkAbortion();
        this.analysis = null;
        //        if (this.showTree) {
        //            graph.showNonModal();
        //        }
        return graph;
    }

    /**
     * Returns a lazy evaluating iterator for the set of instance candidates.
     * @param graph The graph containing the node.
     * @param node The node to find an instance for.
     * @param recursivePredicates The set of recursive predicates.
     * @return A lazy evaluating iterator for the set of instance candidates.
     */
    public Iterable<Node<PrologAbstractState>> generateIteratorForInstanceCandidates(
        final PrologEvaluationGraph graph,
        final Node<PrologAbstractState> node,
        final Map<FunctionSymbol, Integer> recursivePredicates
    ) {
        final Queue<Node<PrologAbstractState>> queue = new ArrayDeque<Node<PrologAbstractState>>();
        //        Set<Node<AbstractState>> instanceChildren = graph.getInstanceChildren(node);
        final AbstractGraphBuilderHeuristic heuristic = this;
        Queue<Node<PrologAbstractState>> toOffer = new ArrayDeque<Node<PrologAbstractState>>();
        if (!graph.getRoot().equals(node)) {
            toOffer.offer(graph.getRoot());
        }
        while (!toOffer.isEmpty()) {
            Node<PrologAbstractState> toCheck = toOffer.poll();
            if (heuristic.instanceCheck(node, toCheck, graph, recursivePredicates)) {
                queue.offer(toCheck);
            } else {
                for (Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getNonInstanceOutEdges(toCheck)) {
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
                        Node<PrologAbstractState> n = queue.poll();
                        Queue<Node<PrologAbstractState>> toOffer = new ArrayDeque<Node<PrologAbstractState>>();
                        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : graph.getNonInstanceOutEdges(n)) {
                            toOffer.offer(edge.getEndNode());
                        }
                        while (!toOffer.isEmpty()) {
                            Node<PrologAbstractState> toCheck = toOffer.poll();
                            if (heuristic.instanceCheck(node, toCheck, graph, recursivePredicates)) {
                                queue.offer(toCheck);
                            } else {
                                for (Edge<AbstractInferenceRule, PrologAbstractState> edge : graph
                                    .getNonInstanceOutEdges(toCheck))
                                {
                                    toOffer.offer(edge.getEndNode());
                                }
                            }
                        }
                        return n;
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
    public void showGraph(boolean show) {
        this.showTree = show;
    }

    @Override
    public void showTime(boolean show) {
        this.showTime = show;
    }

    /**
     * @param graph
     * @param recursiveClauses
     * @param recursivePredicates
     * @param node
     * @param i
     * @param aborter
     * @return
     * @throws AbortionException
     */
    protected abstract boolean expand(
        PrologEvaluationGraph graph,
        Set<Integer> recursiveClauses,
        Map<FunctionSymbol, Integer> recursivePredicates,
        Node<PrologAbstractState> node,
        int i,
        Abortion aborter
    ) throws AbortionException;

    protected Pair<Node<PrologAbstractState>, GeneralizationRule> generalizationStep(
        PrologEvaluationGraph graph,
        Node<PrologAbstractState> node,
        Abortion aborter
    ) {
        PrologAbstractState aState = node.getObject();
        if (aState.getState().size() != 1) {
            return null;
        }
        List<GoalElement> resState = new ArrayList<GoalElement>();
        KnowledgeBase kb = aState.getKnowledgeBase();
        Set<PrologAbstractVariable> newGround = new LinkedHashSet<PrologAbstractVariable>();
        PrologSubstitution replacements = new PrologSubstitution();
        Map<PrologTerm, PrologAbstractVariable> rMap = new LinkedHashMap<PrologTerm, PrologAbstractVariable>();
        for (GoalElement element : aState.getState()) {
            if (!element.isQuestionMark()) {
                PrologTerm originalTerm = element.getTerm();
                PrologTerm replacedTerm = originalTerm;
                for (Occurrence predicationPosition : originalTerm.createListOfPredicationPositions()) {
                    PrologTerm originalPredication = originalTerm.getSubterm(predicationPosition);
                    PrologTerm replacedPredication = originalPredication;
                    for (Occurrence occ : this.calculateGeneralizationPositions(originalPredication)) {
                        PrologTerm toReplace = originalPredication.getSubterm(occ);
                        if (!rMap.containsKey(toReplace)) {
                            PrologAbstractVariable v = graph.getFreshAbstractVariable();
                            replacements.put(v, toReplace);
                            rMap.put(toReplace, v);
                            if (kb.isGround(toReplace)) {
                                kb = kb.setGround(v, true);
                                newGround.add(v);
                            }
                        }
                        if (occ.isEpsilon()) {
                            if (predicationPosition.isEpsilon()) {
                                replacedTerm = rMap.get(toReplace);
                            } else {
                                replacedTerm = replacedTerm.replace(rMap.get(toReplace), predicationPosition);
                            }
                        } else {
                            replacedPredication = replacedPredication.replace(rMap.get(toReplace), occ);
                            replacedTerm = replacedTerm.replace(replacedPredication, predicationPosition);
                        }
                    }
                }
                element = element.replaceTerm(replacedTerm);
            }
            resState.add(element);
        }
        Set<Pair<PrologTerm, PrologTerm>> nonunify = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        for (Pair<PrologTerm, PrologTerm> pair : kb.getNonUnifyingTerms()) {
            PrologTerm t1 = pair.x;
            for (Occurrence occ : this.calculateGeneralizationPositions(pair.x)) {
                PrologTerm toReplace = pair.x.getSubterm(occ);
                if (!rMap.containsKey(toReplace)) {
                    PrologAbstractVariable v = graph.getFreshAbstractVariable();
                    replacements.put(v, toReplace);
                    rMap.put(toReplace, v);
                    if (kb.isGround(toReplace)) {
                        kb = kb.setGround(v, true);
                        newGround.add(v);
                    }
                }
                t1 = t1.replace(rMap.get(toReplace), occ);
            }
            PrologTerm t2 = pair.y;
            for (Occurrence occ : this.calculateGeneralizationPositions(pair.y)) {
                PrologTerm toReplace = pair.y.getSubterm(occ);
                if (!rMap.containsKey(toReplace)) {
                    PrologAbstractVariable v = graph.getFreshAbstractVariable();
                    replacements.put(v, toReplace);
                    rMap.put(toReplace, v);
                    if (kb.isGround(toReplace)) {
                        kb = kb.setGround(v, true);
                        newGround.add(v);
                    }
                }
                t2 = t2.replace(rMap.get(toReplace), occ);
            }
            nonunify.add(new Pair<PrologTerm, PrologTerm>(t1, t2));
        }
        if (replacements.isEmpty()) {
            return null;
        }
        //TODO generalize numbers
        final KnowledgeBase generalizedKnowledgeBase =
            KnowledgeBase.create(
                kb.getGroundSet(),
                kb .getFreeSet(),
                nonunify,
                kb.getIntegerMap(),
                graph.getSMTFactory(),
                graph.getSMTLogic()
            );
        final PrologAbstractState generalizedAbstractState =
            new PrologAbstractState(resState, generalizedKnowledgeBase);
        final GeneralizationRule generalizationRule =
            new GeneralizationRule(
                replacements,
                KnowledgeBase.createWithGroundVars(newGround, graph.getSMTFactory(), graph.getSMTLogic())
            );
        return
            new Pair<Node<PrologAbstractState>, GeneralizationRule>(
                PrologEvaluationGraph.createCleanedNode(generalizedAbstractState),
                generalizationRule
            );
    }

    /**
     * @return
     */
    protected GroundnessAnalysis getGroundnessAnalysis() {
        return this.analysis;
    }

    /**
     * Implements the instance criterion from DA Stroeder (p. 153).
     * @param recursivePredicates The set of recursive predicates.
     * @param child The state to find an instance for.
     * @param parent The state in question to be an instance candidate.
     * @return True if <code>parent</code> satisfies the instance criterion for <code>child</code>.
     */
    protected boolean instanceCriterion(
        Map<FunctionSymbol, Integer> recursivePredicates,
        PrologAbstractState child,
        PrologAbstractState parent
    ) {
        PrologTerm term = child.getHeadOfState().getTerm();
        if (term == null) {
            return false;
        }
        if (term.isConjunction()) {
            term = term.conjunctionHead();
        }
        FunctionSymbol symbol = term.createFunctionSymbol();
        Integer num = recursivePredicates.get(symbol);
        if (num == null) {
            num = PrologBuiltins.RECURSIVE_BUILTIN_PREDICATES.get(symbol);
            if (Globals.useAssertions) {
                assert (num != null) : "This should not happen as we try to find instances "
                    + "only for recursive predicates";
            } else if (num == null) {
                // this should never happen as we try to find instances
                // only for recursive predicates
                return false;
            }
        }
        if (num > this.maxBranchingFactor) {
            return true;
        }
        // alternative/additional ideas:
        // * always allow instances to finite trees
        // * look at substitution to determine if there are function symbols
        //   not occurring in the heads of the recursive predicate's clauses
        Set<PrologVariable> childVars = child.createSetOfAllVariablesInState();
        Set<PrologVariable> parentVars = parent.createSetOfAllVariablesInState();
        int numberOfChildVars = childVars.size();
        int numberOfParentVars = parentVars.size();
        if (numberOfChildVars > numberOfParentVars) {
            return true;
        } else if (numberOfChildVars == numberOfParentVars) {
            int numberOfAbstractChildVars = 0;
            int numberOfAbstractParentVars = 0;
            for (PrologVariable var : childVars) {
                if (var.isAbstractVariable()) {
                    numberOfAbstractChildVars++;
                }
            }
            for (PrologVariable var : parentVars) {
                if (var.isAbstractVariable()) {
                    numberOfAbstractParentVars++;
                }
            }
            return numberOfAbstractChildVars >= numberOfAbstractParentVars;
        } else {
            return false;
        }
    }

    /**
     * Calculates a set of Occurences where the specified term can
     * generalized according to the specified maximum nested depth
     * and generalization depth.
     * @param term The term to generalize.
     * @param maxGeneralizationDepth The maximum nested depth.
     * @param generalizationDepth The generalization depth.
     * @return A set of Occurences where the specified term can be
     *         generalized.
     */
    private Set<Occurrence> calculateGeneralizationPositions(PrologTerm term) {
        Set<Occurrence> res = new LinkedHashSet<Occurrence>();
        Occurrence position = new Occurrence();
        Map<FunctionSymbol, List<Occurrence>> occurences = new LinkedHashMap<FunctionSymbol, List<Occurrence>>();
        this.calculateGeneralizationPositions(term, term, position, occurences, res);
        Occurrence.reduceToSmallest(res);
        return res;
    }

    /**
     * @param term
     * @param position
     * @param symbolCount
     * @param firstOccurence
     * @param res
     */
    private void calculateGeneralizationPositions(
        PrologTerm originalTerm,
        PrologTerm term,
        Occurrence position,
        Map<FunctionSymbol, List<Occurrence>> occurrences,
        Set<Occurrence> res
    ) {
        if (term.isConjunction() || term.isDisjunctionTerm() || term.isIf()) {
            this.calculateGeneralizationPositionsForChildren(originalTerm, term, position, occurrences, res);
        } else {
            FunctionSymbol symbol = term.createFunctionSymbol();
            if (!occurrences.containsKey(symbol)) {
                occurrences.put(symbol, new ArrayList<Occurrence>());
            }
            List<Occurrence> list = occurrences.get(symbol);
            list.add(position);
            int count = occurrences.get(symbol).size();
            if (count > this.generalizationDepth) {
                res.add(list.get(this.generalizationPosition - 1));
            }
            this.calculateGeneralizationPositionsForChildren(originalTerm, term, position, occurrences, res);
            list.remove(position);
        }
    }

    /**
     * @param originalTerm
     * @param term
     * @param symbolCount
     * @param firstOccurence
     * @param res
     */
    private void calculateGeneralizationPositionsForChildren(
        PrologTerm originalTerm,
        PrologTerm term,
        Occurrence position,
        Map<FunctionSymbol, List<Occurrence>> occurrences,
        Set<Occurrence> res
    ) {
        for (int i = 0; i < term.getArity(); i++) {
            this.calculateGeneralizationPositions(
                originalTerm,
                term.getArgument(i),
                position.appendChildNumber(i),
                occurrences,
                res
            );
        }
    }

    /**
     * Performs all checks for an instance candidate.
     * @param node The node to find an instance for.
     * @param toCheck The node in question to be an instance candidate.
     * @param graph The graph containing the nodes.
     * @param recursivePredicates The set of recursive predicates.
     * @return True if <code>toCheck</code> is an instance candidate.
     */
    private boolean instanceCheck(
        Node<PrologAbstractState> node,
        Node<PrologAbstractState> toCheck,
        PrologEvaluationGraph graph,
        Map<FunctionSymbol, Integer> recursivePredicates
    ) {
        FunctionSymbol symbol = node.getObject().getHeadOfState().getTerm().createFunctionSymbol();
        GoalElement element = toCheck.getObject().getHeadOfState();
        return
            !node.equals(toCheck)
            && element != null
            && !element.hasApplicableClause()
            && !element.isQuestionMark()
            && element.getTerm().createFunctionSymbol().equals(symbol)
            //&& this.instanceCriterion(recursivePredicates, node.getObject(), toCheck.getObject())
            && (
                AbstractGraphBuilderHeuristic.NO_INSTANCE_CHAINS ?
                    !(graph.isInstanceNode(toCheck) || graph.isGeneralizationNode(toCheck)) :
                        graph.noInstanceOrGeneralizationPath(toCheck, node)
            );
    }

}
