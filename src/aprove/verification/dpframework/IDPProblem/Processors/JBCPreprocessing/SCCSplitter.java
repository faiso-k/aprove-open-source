package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This processor tries to find subcycles in the parts of the ITRS that later
 * results in the DP graph. If successful, the subcycle will be modified such
 * that the resulting IDP will represent it using rules, not as a subcycle in
 * the DP graph.
 * @author cotto
 */
public class SCCSplitter extends ITRSProcessor {
    /**
     * Just a wrapper for a lot of values.
     * @author cotto
     */
    public class TodoThing {

        final MultiGraph<FunctionSymbol, GeneralizedRule> graph;
        final Cycle<FunctionSymbol> scc;
        final Cycle<FunctionSymbol> sccInner;
        final Cycle<FunctionSymbol> sccOuter;
        final CollectionMap<FunctionSymbol, Integer> map;
        final GeneralizedRule specialRule;
        final ITRSProblem itrs;

        public TodoThing(final ITRSProblem itrs, final MultiGraph<FunctionSymbol, GeneralizedRule> graph,
                final Cycle<FunctionSymbol> scc, final Cycle<FunctionSymbol> sccInner,
                final Cycle<FunctionSymbol> sccOuter, final CollectionMap<FunctionSymbol, Integer> map,
                final GeneralizedRule specialRule) {
            this.itrs = itrs;
            this.graph = graph;
            this.scc = scc;
            this.sccInner = sccInner;
            this.sccOuter = sccOuter;
            this.map = map;
            this.specialRule = specialRule;
        }
    }

    /**
     * The Proof.
     * @author cotto
     */
    public class SCCSplitterProof extends DefaultProof {

        /**
         * @return the proof
         * @param o some export util
         * @param level verbosity level, unused
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Obvious.";
        }
    }

    /**
     * Yes, we can. For innermost ITRSs.
     * @param itrs any itrs problem
     * @return true (sometimes)
     */
    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return itrs.isNfQSubsetEqNfR();
    }

    /**
     * Take care of the ITRS and rip it apart.
     * @param itrs some ITRS problem
     * @param aborter an aborter
     * @return a equivalent ITRS where some rules are changed such that a
     * subcycle is transformed to a method invcation (if successful)
     * @throws AbortionException never.
     */
    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter) throws AbortionException {
        // First, check the ITRS and get its SCCs with interesting nodes
        final Pair<MultiGraph<FunctionSymbol, GeneralizedRule>, Collection<Cycle<FunctionSymbol>>> pair =
            HelperClass.toGraph(itrs, true);
        if (pair == null) {
            return ResultFactory.unsuccessful();
        }
        final Collection<Cycle<FunctionSymbol>> sccs = pair.y;
        final MultiGraph<FunctionSymbol, GeneralizedRule> graph = pair.x;

        int bestSize = 0;
        TodoThing bestTodo = null;
        for (final Cycle<FunctionSymbol> scc : sccs) {
            final Collection<Node<FunctionSymbol>> interestingNodes = scc.getInterestingNodes();
            if (interestingNodes == null || interestingNodes.isEmpty()) {
                continue;
            }
            NODE: for (final Node<FunctionSymbol> interestingNode : interestingNodes) {
                /*
                 * This node should be a node where two SCCs meet. If this is
                 * the case, compute how many arguments are left unchanged in
                 * each of these two SCCs. Splitting is done by removing a
                 * single outgoing edge and re-computing the SCCs. The other
                 * SCC is computed by only allowing the previously removed
                 * outgoing edge and re-computing the SCCs.
                 */
                final MultiGraph<FunctionSymbol, GeneralizedRule> sccGraph = graph.getSubGraph(scc);
                final Set<EdgeEquality<GeneralizedRule, FunctionSymbol>> outEdges =
                    sccGraph.getOutEdges(interestingNode);
                assert (!outEdges.isEmpty());
                final EdgeEquality<GeneralizedRule, FunctionSymbol> someEdge = outEdges.iterator().next();
                final Node<FunctionSymbol> someEdgeSource = someEdge.getStartNode();
                final Node<FunctionSymbol> someEdgeDest = someEdge.getEndNode();
                final Collection<GeneralizedRule> someEdgeLabels = someEdge.getObject();
                assert (someEdgeLabels.size() == 1);
                final GeneralizedRule specialRule = someEdge.getObject().iterator().next();
                // Allow every edge, but not someEdge
                final EdgeFilter<Collection<GeneralizedRule>, FunctionSymbol> filterOne =
                    new EdgeFilter<Collection<GeneralizedRule>, FunctionSymbol>() {
                        @Override
                        public boolean selectEdge(final Node<FunctionSymbol> source,
                            final Node<FunctionSymbol> dest,
                            final Collection<GeneralizedRule> labels) {
                            return !someEdgeSource.equals(source) || !someEdgeDest.equals(dest)
                                || !someEdgeLabels.equals(labels);
                        }
                    };
                final Collection<Cycle<FunctionSymbol>> sccsOne = sccGraph.getSCCs(filterOne);
                Cycle<FunctionSymbol> sccOne = null;
                for (final Cycle<FunctionSymbol> cycle : sccsOne) {
                    if (cycle.contains(interestingNode)) {
                        if (sccOne != null) {
                            continue NODE;
                        }
                        sccOne = cycle;
                    }
                }
                if (sccOne == null) {
                    continue;
                }
                // Allow every edge, but for the interestingNode only the outgoing edge someEdge
                final EdgeFilter<Collection<GeneralizedRule>, FunctionSymbol> filterTwo =
                    new EdgeFilter<Collection<GeneralizedRule>, FunctionSymbol>() {
                        @Override
                        public boolean selectEdge(final Node<FunctionSymbol> source,
                            final Node<FunctionSymbol> dest,
                            final Collection<GeneralizedRule> labels) {
                            if (source.equals(interestingNode)) {
                                return dest.equals(someEdgeDest) && someEdgeLabels.equals(labels);
                            }
                            return true;
                        }
                    };
                final Collection<Cycle<FunctionSymbol>> sccsTwo = sccGraph.getSCCs(filterTwo);
                Cycle<FunctionSymbol> sccTwo = null;
                for (final Cycle<FunctionSymbol> cycle : sccsTwo) {
                    if (cycle.contains(interestingNode)) {
                        if (sccTwo != null) {
                            continue NODE;
                        }
                        sccTwo = cycle;
                    }
                }
                if (sccTwo == null || sccOne.size() + sccTwo.size() != scc.size() + 1) {
                    continue NODE;
                }
                /*
                 * Okay, this split sounds OK. Now test if it actually allows us
                 * to remove arguments.
                 */
                final CollectionMap<FunctionSymbol, Integer> mapOne = HelperClass.getUnchangedPositions(graph, sccOne);
                final CollectionMap<FunctionSymbol, Integer> mapTwo = HelperClass.getUnchangedPositions(graph, sccTwo);
                boolean useOne = true;
                int size = 0;
                if (mapOne.isEmpty()) {
                    if (mapTwo.isEmpty()) {
                        continue;
                    }
                    final Collection<Integer> firstTwo = mapTwo.entrySet().iterator().next().getValue();
                    useOne = false;
                    size = firstTwo.size();
                } else if (!mapTwo.isEmpty()) {
                    final Collection<Integer> firstOne = mapOne.entrySet().iterator().next().getValue();
                    final Collection<Integer> firstTwo = mapTwo.entrySet().iterator().next().getValue();
                    size = firstOne.size();
                    final int sizeTwo = firstTwo.size();
                    if (sizeTwo > size) {
                        useOne = false;
                        size = sizeTwo;
                    }
                } else {
                    size = mapOne.entrySet().iterator().next().getValue().size();
                }
                /*
                 * We only want to do one split for each processor invocation.
                 * Choose the best one.
                 */
                if (size > bestSize) {
                    bestSize = size;
                    if (useOne) {
                        bestTodo = new TodoThing(itrs, graph, scc, sccOne, sccTwo, mapOne, specialRule);
                    } else {
                        bestTodo = new TodoThing(itrs, graph, scc, sccTwo, sccOne, mapTwo, specialRule);
                    }
                }
            }
        }
        if (bestSize > 0) {
            return this.doTheSplit(bestTodo);
        }
        return ResultFactory.unsuccessful();
    }

    /**
     * For the given special rule and the corresponding two subcycles, do the
     * split.
     * @param todoThing everything related to the split position
     * @return the resulting ITRS with some proof.
     */
    private Result doTheSplit(final TodoThing todoThing) {
        final ITRSProblem itrs = todoThing.itrs;
        final MultiGraph<FunctionSymbol, GeneralizedRule> graph = todoThing.graph;
        final Cycle<FunctionSymbol> scc = todoThing.scc;
        final Cycle<FunctionSymbol> sccOne = todoThing.sccInner;
        final Cycle<FunctionSymbol> sccTwo = todoThing.sccOuter;
        final CollectionMap<FunctionSymbol, Integer> map = todoThing.map;
        final GeneralizedRule specialRule = todoThing.specialRule;
        final MultiGraph<FunctionSymbol, GeneralizedRule> subGraphOne = graph.getSubGraph(sccOne);
        final MultiGraph<FunctionSymbol, GeneralizedRule> subGraphTwo = graph.getSubGraph(sccTwo);
        final Collection<GeneralizedRule> rulesOne = new LinkedHashSet<GeneralizedRule>();
        final Collection<GeneralizedRule> rulesTwo = new LinkedHashSet<GeneralizedRule>();
        for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : subGraphOne.getEdges()) {
            rulesOne.addAll(edge.getObject());
        }
        for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : subGraphTwo.getEdges()) {
            rulesTwo.addAll(edge.getObject());
        }
        final ITRSProblem subItrsOne =
            ITRSProblem.create(rulesOne, new IQTermSet(HelperClass.getNewQ(rulesOne), IDPPredefinedMap.DEFAULT_MAP));
        final ITRSProblem subItrsTwo =
            ITRSProblem.create(rulesTwo, new IQTermSet(HelperClass.getNewQ(rulesTwo), IDPPredefinedMap.DEFAULT_MAP));
        /*
         * This seems to be promising. Before we continue, get the rules
         * of the other SCCs (of any?) and mark all function symbols as
         * "in use".
         */
        final Collection<FunctionSymbol> takenSymbols = new LinkedHashSet<FunctionSymbol>();
        final Collection<GeneralizedRule> rulesNotOnThisSCC = new LinkedHashSet<GeneralizedRule>(itrs.getR());
        for (final Node<FunctionSymbol> node : scc) {
            for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : graph.getOutEdges(node)) {
                rulesNotOnThisSCC.removeAll(edge.getObject());
            }
        }
        HelperClass.mark(rulesNotOnThisSCC, takenSymbols);

        final Pair<ITRSProblem, Map<FunctionSymbol, FunctionSymbol>> newItrsOne;
        final Collection<GeneralizedRule> newRulesOne = new LinkedHashSet<GeneralizedRule>();
        final Collection<GeneralizedRule> newRulesTwo = new LinkedHashSet<GeneralizedRule>();
        HelperClass.mark(subItrsTwo.getR(), takenSymbols);
        newItrsOne = HelperClass.getResultingITRS(subItrsOne, map, takenSymbols);
        newRulesOne.addAll(newItrsOne.x.getR());
        newRulesTwo.addAll(subItrsTwo.getR());
        newRulesTwo.addAll(rulesNotOnThisSCC);
        this.split(newRulesOne, newRulesTwo, newItrsOne.y, map, specialRule, takenSymbols);
        final Collection<GeneralizedRule> allNewRules = new LinkedHashSet<GeneralizedRule>(newRulesOne);
        allNewRules.addAll(newRulesTwo);
        assert (allNewRules.size() > itrs.getR().size());
        final ITRSProblem newProblem =
            ITRSProblem.create(allNewRules, new IQTermSet(HelperClass.getNewQ(allNewRules),
                IDPPredefinedMap.DEFAULT_MAP));
        return ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT, new SCCSplitterProof());
    }

    /**
     * Modify the two rule sets. For the rule set corresponding to the subcycle
     * a single rule is added. This rule is used to leave the subcycle and go
     * back to the outer cycle. To build this rule, we take the LHS of the
     * special rule (which was used to split the SCC into two parts) and strip
     * away the unchanged arguments, resulting in lhs'. The arguments that are
     * left are used for the new LHS. The new RHS is built using a tuple symbol,
     * where all the arguments of the new LHS are stored without any change.
     * <p>
     * For the outer cycle, all rules with a RHS that corresponds to the LHS of
     * the special rule are changed. Here, we only leave the arguments that are
     * unchanged in the subcycle and add a term calling the function defined by
     * the subcycle (which is the stripped version of the LHS of the special
     * rule). Furthermore, for every rule with a LHS that corresponds to the LHS
     * of the special rule, we also restrict to the arguments that are left
     * unchanged in the subcycle and add the tuple term generated for the
     * subcycle.
     * @param rulesSub add lhs'(...) -> tuple(...) here
     * @param rulesOuter add f(...) -> g(..., lhs'(...)) and g(..., tuple(...))
     * -> h(...) here
     * @param renamedSymbols the renaming done so far
     * @param map unused arguments
     * @param specialRule the special rule used to split the SCCs
     * @param takenSymbols the symbols that are already in use
     */
    private void split(final Collection<GeneralizedRule> rulesSub,
        final Collection<GeneralizedRule> rulesOuter,
        final Map<FunctionSymbol, FunctionSymbol> renamedSymbols,
        final CollectionMap<FunctionSymbol, Integer> map,
        final GeneralizedRule specialRule,
        final Collection<FunctionSymbol> takenSymbols) {
        // get the LHS of the special rule
        final TRSFunctionApplication specialLHS = specialRule.getLeft();
        final FunctionSymbol specialFS = specialLHS.getRootSymbol();
        final int specialArity = specialFS.getArity();

        // Construct the stripped version of the LHS of the special rule (lhs')
        final FunctionSymbol specialStrippedFS = renamedSymbols.get(specialFS);
        final int specialStrippedArity = specialStrippedFS.getArity();
        final ArrayList<TRSTerm> specialStrippedArgs = new ArrayList<TRSTerm>(specialStrippedArity);
        final Collection<Integer> specialUnchangedArgs = map.get(specialFS);
        for (int i = 0; i < specialArity; i++) {
            if (!specialUnchangedArgs.contains(Integer.valueOf(i))) {
                final TRSTerm arg = specialLHS.getArgument(i);
                specialStrippedArgs.add(arg);
            }
        }
        final TRSFunctionApplication strippedFA =
            TRSTerm.createFunctionApplication(specialStrippedFS, specialStrippedArgs);

        // Construct the tuple term
        FunctionSymbol tupleFS = FunctionSymbol.create("tuple", specialStrippedArity);
        int counter = 2;
        while (takenSymbols.contains(tupleFS)) {
            tupleFS = FunctionSymbol.create("tuple" + counter, specialStrippedArity);
            counter++;
        }
        takenSymbols.add(tupleFS);
        final TRSFunctionApplication tupleFA = TRSTerm.createFunctionApplication(tupleFS, specialStrippedArgs);

        // add lhs'(...) -> tuple(...) to the rules for the subcycle
        rulesSub.add(Rule.create(strippedFA, tupleFA));

        // Now have a look at the rules of the outer cycle
        final CollectionMap<GeneralizedRule, GeneralizedRule> replaceRules =
            new CollectionMap<GeneralizedRule, GeneralizedRule>();
        /*
         * This symbol will be used as the LHs of the special rule, where only
         * the unchanged arguments are left and an addition argument for
         * lhs'/tuple is added
         */
        // arity: All args - the ones not removed (in the inner cycle) + one new for the tuple
        final int argsReplacedByTupleArity = specialArity - specialStrippedArity + 1;
        final String newName = "SPLIT_" + specialFS.getName();
        FunctionSymbol outerSymbol = FunctionSymbol.create(newName, argsReplacedByTupleArity);
        final int i = 2;
        while (takenSymbols.contains(outerSymbol)) {
            outerSymbol = FunctionSymbol.create(newName + i, argsReplacedByTupleArity);
            counter++;
        }
        takenSymbols.add(outerSymbol);

        for (final GeneralizedRule rule : rulesOuter) {
            final TRSFunctionApplication lhs = rule.getLeft();
            if (lhs.getRootSymbol().equals(specialFS)) {
                // remove the arguments changed by the subcycle, add the tuple term instead
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(outerSymbol.getArity());
                final TRSFunctionApplication specialLeft = specialRule.getLeft();
                for (int iterator = 0; iterator < specialArity; iterator++) {
                    if (specialUnchangedArgs.contains(Integer.valueOf(iterator))) {
                        args.add(specialLeft.getArgument(iterator));
                    }
                }
                args.add(tupleFA);
                replaceRules.add(rule,
                    Rule.create(TRSTerm.createFunctionApplication(outerSymbol, args), rule.getRight()));
            }
            final TRSTerm rhs = rule.getRight();
            assert (rhs instanceof TRSFunctionApplication);
            final TRSFunctionApplication rightFA = (TRSFunctionApplication) rhs;
            if (rightFA.getRootSymbol().equals(specialFS)) {
                // append the call to the function generating the tuple
                final ArrayList<TRSTerm> newArgsRight = new ArrayList<TRSTerm>(argsReplacedByTupleArity);
                final ArrayList<TRSTerm> shortArgs = new ArrayList<TRSTerm>(specialStrippedArity);
                for (int iterator = 0; iterator < specialArity; iterator++) {
                    if (specialUnchangedArgs.contains(Integer.valueOf(iterator))) {
                        newArgsRight.add(rightFA.getArgument(iterator));
                    } else {
                        shortArgs.add(rightFA.getArgument(iterator));
                    }
                }
                final TRSFunctionApplication shortRight =
                    TRSTerm.createFunctionApplication(specialStrippedFS, shortArgs);
                newArgsRight.add(shortRight);

                final TRSFunctionApplication newRight =
                    TRSTerm.createFunctionApplication(outerSymbol, newArgsRight);
                final GeneralizedRule newRule = Rule.create(rule.getLeft(), newRight);
                replaceRules.add(rule, newRule);
            }
        }
        assert (!replaceRules.isEmpty());
        for (final Map.Entry<GeneralizedRule, Collection<GeneralizedRule>> entry : replaceRules.entrySet()) {
            final boolean removed = rulesOuter.remove(entry.getKey());
            assert (removed);
            for (final GeneralizedRule addRule : entry.getValue()) {
                final boolean added = rulesOuter.add(addRule);
                assert (added);
            }
        }
    }

}
