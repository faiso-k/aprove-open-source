package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author cryingshadow
 * Class gathering methods to generate TRS rules from paths or nodes in a derivation graph.
 */
public abstract class RuleConstructor {

    /**
     * Computes a set of rules simulating all evaluations along the specified
     * path.
     * @param path The path to simulate.
     * @param graph The graph containing the path.
     * @param ground The groundness analysis function.
     * @param fridge Fresh names come out of the fridge...
     * @param aborter For abortions...
     * @return A set of rules simulating all evaluations along the specified
     *         path.
     * @throws AbortionException If the computation is aborted...
     */
    public static Set<Rule> buildConnectionRules(
        final List<Node<PrologAbstractState>> path,
        final PrologEvaluationGraph graph,
        final GroundnessAnalysis ground,
        final FreshNameGenerator fridge,
        final Abortion aborter) throws AbortionException
    {
        final Set<Rule> res = new LinkedHashSet<Rule>();
        final PrologSubstitution sigma0 = PrologGraphProcessor.getSubstitutionForPath(graph, path, 0, aborter);
        final Node<PrologAbstractState> first = path.get(0);
        final Node<PrologAbstractState> last = path.get(path.size() - 1);
        if (graph.isSuccessNode(last)) {
            res.add(Rule
                .create(
                    (TRSFunctionApplication) RuleConstructor
                        .renameIn(first, graph, fridge)
                        .applySubstitution(sigma0)
                        .toTerm(),
                    RuleConstructor
                        .renameOut(first, RuleConstructor.compSkip(path, 1, graph, aborter), graph, ground, fridge)
                        .applySubstitution(sigma0)
                        .toTerm()));
        } else {
            final PrologTerm in = RuleConstructor.renameIn(first, graph, fridge);
            final Set<PrologVariable> vars = in.createSetOfAllVariables();
            final ArrayList<TRSTerm> args1 = new ArrayList<TRSTerm>();
            args1.add(RuleConstructor.renameIn(last, graph, fridge).toTerm());
            for (final PrologVariable v : vars) {
                final TRSTerm t = v.applySubstitution(sigma0).toTerm();
                args1.add(t);
            }
            final FunctionSymbol u = FunctionSymbol.create(fridge.getFreshName("U", false), args1.size());
            res.add(Rule.create(
                (TRSFunctionApplication) in.applySubstitution(sigma0).toTerm(),
                TRSTerm.createFunctionApplication(u, args1)));
            for (int i = 1; i <= last.getObject().getState().size(); i++) {
                if (!last.getObject().getState().get(i - 1).isQuestionMark()) {
                    final PrologSubstitution sigma =
                        PrologGraphProcessor.getSubstitutionForPath(graph, path, i - 1, aborter);
                    final ArrayList<TRSTerm> args2 = new ArrayList<TRSTerm>();
                    args2.add(RuleConstructor.renameOut(last, i, graph, ground, fridge).toTerm());
                    for (final PrologVariable v : vars) {
                        args2.add(v.applySubstitution(sigma).toTerm());
                    }
                    res.add(Rule.create(
                        TRSTerm.createFunctionApplication(u, args2),
                        RuleConstructor
                            .renameOut(first, RuleConstructor.compSkip(path, i, graph, aborter), graph, ground, fridge)
                            .applySubstitution(sigma)
                            .toTerm()));
                }
            }
        }
        return res;
    }

    /**
     * Computes a set of rules simulating all evaluations at a PARALLEL node.
     * renin(parallel) -> U(renin(p1),renin(p2),V(\renin(parallel)))
     * U(renout(p1),x,V(renin(parallel))) -> renout(parallel)
     * U(x,renout(p2),V(renin(parallel))) -> renout(parallel)
     * This is ok as long as we only consider ground variables - otherwise we would need to consider the possibility
     * that a substitution is backtracked by a PARALLEL node.
     * @param parallel The PARALLEL node to consider.
     * @param graph The graph containing the node.
     * @param ground A groundness analysis function.
     * @param fridge Fresh names come out of the fridge...
     * @param aborter For abortions...
     * @return A set of rules simulating all evaluations at a PARALLEL node.
     * @throws AbortionException If it is aborted...
     */
    public static Set<Rule> buildParallelRules(
        final Node<PrologAbstractState> parallel,
        final PrologEvaluationGraph graph,
        final GroundnessAnalysis ground,
        final FreshNameGenerator fridge,
        final Abortion aborter) throws AbortionException
    {
        final Set<Rule> res = new LinkedHashSet<Rule>();
        final Node<PrologAbstractState> p1 = graph.getFirstChild(parallel);
        final Node<PrologAbstractState> p2 = graph.getLastChild(parallel);
        final ArrayList<TRSTerm> argsUR1right = new ArrayList<TRSTerm>();
        final PrologTerm inN = RuleConstructor.renameIn(parallel, graph, fridge);
        final Set<PrologVariable> vars = inN.createSetOfAllVariables();
        aborter.checkAbortion();
        argsUR1right.add(RuleConstructor.renameIn(p1, graph, fridge).toTerm());
        argsUR1right.add(RuleConstructor.renameIn(p2, graph, fridge).toTerm());
        for (final PrologVariable v : vars) {
            final TRSTerm t = v.toTerm();
            argsUR1right.add(t);
        }
        final FunctionSymbol u = FunctionSymbol.create(fridge.getFreshName("U", false), argsUR1right.size());
        res.add(Rule.create((TRSFunctionApplication) inN.toTerm(), TRSTerm.createFunctionApplication(u, argsUR1right)));
        final int m = p1.getObject().getState().size();
        for (int j = 1; j <= m; j++) {
            if (!p1.getObject().getState().get(j - 1).isQuestionMark()) {
                aborter.checkAbortion();
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(RuleConstructor.renameOut(p1, j, graph, ground, fridge).toTerm());
                args.add(TRSTerm.createVariable(fridge.getFreshName("X", false)));
                for (final PrologVariable v : vars) {
                    args.add(v.toTerm());
                }
                res.add(Rule.create(
                    TRSTerm.createFunctionApplication(u, args),
                    RuleConstructor.renameOut(parallel, j, graph, ground, fridge).toTerm()));
            }
        }
        for (int i = 1; i <= p2.getObject().getState().size(); i++) {
            if (!p2.getObject().getState().get(i - 1).isQuestionMark()) {
                aborter.checkAbortion();
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(TRSTerm.createVariable(fridge.getFreshName("X", false)));
                args.add(RuleConstructor.renameOut(p2, i, graph, ground, fridge).toTerm());
                for (final PrologVariable v : vars) {
                    args.add(v.toTerm());
                }
                res.add(Rule.create(
                    TRSTerm.createFunctionApplication(u, args),
                    RuleConstructor.renameOut(parallel, m + i, graph, ground, fridge).toTerm()));
            }
        }
        return res;
    }

    /**
     * Computes a set of rules simulating all evaluations at a SPLIT node.
     * @param split The SPLIT node to consider.
     * @param graph The graph containing the node.
     * @param ground A groundness analysis function.
     * @param complexity Flag indicating whether the rules are constructed for complexity or termination analysis.
     * @param fridge Fresh names come out of the fridge...
     * @param aborter For abortions...
     * @return A set of rules simulating all evaluations at a SPLIT node.
     * @throws AbortionException If it is aborted...
     */
    public static Set<Rule> buildSplitRules(
        final Node<PrologAbstractState> split,
        final PrologEvaluationGraph graph,
        final GroundnessAnalysis ground,
        final boolean complexity,
        final FreshNameGenerator fridge,
        final Abortion aborter) throws AbortionException
    {
        final Set<Rule> res = new LinkedHashSet<Rule>();
        final Node<PrologAbstractState> s1 = graph.getFirstChild(split);
        final Node<PrologAbstractState> s2 = graph.getLastChild(split);
        final PrologSubstitution delta = ((SplitRule) graph.getEdgeObject(split, s2)).getSplitCase().getReplacements();
        aborter.checkAbortion();
        final ArrayList<TRSTerm> args11 = new ArrayList<TRSTerm>();
        final ArrayList<TRSTerm> args12 = new ArrayList<TRSTerm>();
        final ArrayList<TRSTerm> args21 = new ArrayList<TRSTerm>();
        final ArrayList<TRSTerm> args22 = new ArrayList<TRSTerm>();
        final PrologTerm in = RuleConstructor.renameIn(split, graph, fridge);
        final Set<PrologVariable> vars = in.createSetOfAllVariables();
        final PrologTerm in1 = RuleConstructor.renameIn(s1, graph, fridge);
        final TRSTerm in1t = in1.applySubstitution(delta).toTerm();
        final PrologTerm out1 = RuleConstructor.renameOut(s1, 1, graph, ground, fridge);
        args11.add(in1t);
        args12.add(out1.applySubstitution(delta).toTerm());
        if (complexity
            && graph.canReachNode(split, split, aborter)
            && PrologToComplexityProblemTransformer.hasPotentialComplexityIncreaseAfterSuccess(s1, graph, aborter))
        {
            args11.add(in1t);
            args12.add(TRSTerm.createVariable(fridge.getFreshName("X", false)));
        }
        args21.add(RuleConstructor.renameIn(s2, graph, fridge).toTerm());
        args22.add(RuleConstructor.renameOut(s2, 1, graph, ground, fridge).toTerm());
        for (final PrologVariable v : vars) {
            final TRSTerm t = v.applySubstitution(delta).toTerm();
            args11.add(t);
            args12.add(t);
            args21.add(t);
            args22.add(t);
        }
        for (final PrologVariable v : out1.createSetOfAllVariables()) {
            aborter.checkAbortion();
            if (!vars.contains(v)) {
                final TRSTerm t = v.applySubstitution(delta).toTerm();
                args21.add(t);
                args22.add(t);
            }
        }
        final FunctionSymbol u1 = FunctionSymbol.create(fridge.getFreshName("U", false), args11.size());
        final FunctionSymbol u2 = FunctionSymbol.create(fridge.getFreshName("U", false), args21.size());
        res.add(Rule.create(
            (TRSFunctionApplication) in.applySubstitution(delta).toTerm(),
            TRSTerm.createFunctionApplication(u1, args11)));
        res.add(Rule.create(TRSTerm.createFunctionApplication(u1, args12), TRSTerm.createFunctionApplication(u2, args21)));
        res.add(Rule.create(
            TRSTerm.createFunctionApplication(u2, args22),
            RuleConstructor.renameOut(split, 1, graph, ground, fridge).applySubstitution(delta).toTerm()));
        return res;
    }

    /**
     * Computes the renin function, i.e., computes an input term for the
     * specified node.
     * @param node The node to encode as term.
     * @param graph The graph containing the node.
     * @param fridge Fresh names come out of the fridge...
     * @return An input term for the specified node.
     */
    public static PrologTerm renameIn(
        final Node<PrologAbstractState> node,
        final PrologEvaluationGraph graph,
        final FreshNameGenerator fridge)
    {
        if (graph.isInstanceNode(node)) {
            final Node<PrologAbstractState> child = graph.getFirstChild(node);
            final PrologTerm res = RuleConstructor.renameIn(child, graph, fridge);
            final InstanceRule step = (InstanceRule) graph.getEdgeObject(node, child);
            final PrologSubstitution mu = step.getMatcher();
            return res.applySubstitution(mu);
        } else if (graph.isGeneralizationNode(node)) {
            final Node<PrologAbstractState> child = graph.getFirstChild(node);
            final PrologTerm res = RuleConstructor.renameIn(child, graph, fridge);
            final GeneralizationRule step = (GeneralizationRule) graph.getEdgeObject(node, child);
            final PrologSubstitution mu = step.getGeneralizationAsSubstitution();
            return res.applySubstitution(mu);
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            final KnowledgeBase kb = node.getObject().getKnowledgeBase();
            for (final PrologVariable var : node.getObject().createSetOfAllVariablesInState()) {
                if (kb.isGround(var)) {
                    args.add(var);
                }
            }
            return new PrologTerm(fridge.getFreshName("f" + node.getNodeNumber() + "_in", true), args);
        }
    }

    /**
     * Computes the renout function, i.e., computes an output term for the
     * specified node and goal index.
     * @param node The node to encode as term.
     * @param goal The index of the goal for the term encoding.
     * @param graph The graph containing the node.
     * @param ground A groundness analysis function.
     * @param fridge Fresh names come out of the fridge...
     * @return An output term for the specified node and goal index.
     */
    public static PrologTerm renameOut(
        final Node<PrologAbstractState> node,
        final int goal,
        final PrologEvaluationGraph graph,
        final GroundnessAnalysis ground,
        final FreshNameGenerator fridge)
    {
        assert (node.getObject().getState().size() >= goal) : "The goal index is out of bounds!";
        if (graph.isInstanceNode(node)) {
            final Node<PrologAbstractState> child = graph.getFirstChild(node);
            final PrologTerm res = RuleConstructor.renameOut(child, goal, graph, ground, fridge);
            final InstanceRule step = (InstanceRule) graph.getEdgeObject(node, child);
            final PrologSubstitution mu = step.getMatcher();
            return res.applySubstitution(mu);
        } else if (graph.isGeneralizationNode(node)) {
            final Node<PrologAbstractState> child = graph.getFirstChild(node);
            final PrologTerm res = RuleConstructor.renameOut(child, goal, graph, ground, fridge);
            final GeneralizationRule step = (GeneralizationRule) graph.getEdgeObject(node, child);
            final PrologSubstitution mu = step.getGeneralizationAsSubstitution();
            return res.applySubstitution(mu);
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            final PrologAbstractState state = node.getObject();
            final Set<PrologVariable> groundVars = new LinkedHashSet<PrologVariable>();
            final KnowledgeBase kb = node.getObject().getKnowledgeBase();
            for (final PrologVariable var : node.getObject().createSetOfAllVariablesInState()) {
                if (kb.isGround(var)) {
                    groundVars.add(var);
                }
            }
            final Set<PrologVariable> initialGroundVars = new LinkedHashSet<PrologVariable>(groundVars);
            final PrologTerm t = state.getState().get(goal - 1).getTerm();
            if (t != null) {
                for (final PrologTerm conjunct : t.createConjunctionListOfPredications()) {
                    //TODO extend to OR and IF
                    final Set<Integer> groundPositions = new LinkedHashSet<Integer>();
                    for (int i = 0; i < conjunct.getArity(); i++) {
                        if (conjunct.getArgument(i).containsOnlyVariablesFrom(groundVars)) {
                            groundPositions.add(i);
                        }
                    }
                    final Set<Integer> analysis =
                        ground.getGroundPositions(conjunct.createFunctionSymbol(), groundPositions);
                    for (final Integer i : analysis) {
                        groundVars.addAll(conjunct.getArgument(i).createSetOfAllVariables());
                    }
                }
            }
            groundVars.removeAll(initialGroundVars);
            for (final PrologVariable var : groundVars) {
                args.add(var);
            }
            return new PrologTerm(fridge.getFreshName("f" + node.getNodeNumber() + "_out" + goal, true), args);
        }
    }

    /**
     * Computes the skip function, i.e., which backtracking goal at the
     * beginning of the specified path belongs to the i-th backtracking goal at
     * the end of the path.
     * @param path The path to consider.
     * @param i The index of the goal at the end of the path.
     * @param graph The graph containing the path.
     * @param aborter For abortions...
     * @return The value of the skip function.
     * @throws AbortionException If it is aborted...
     */
    public static int compSkip(
        final List<Node<PrologAbstractState>> path,
        final int i,
        final PrologEvaluationGraph graph,
        final Abortion aborter) throws AbortionException
    {
        if (path.size() > 1) {
            // otherwise return i
            aborter.checkAbortion();
            final List<Node<PrologAbstractState>> restPath = new ArrayList<Node<PrologAbstractState>>();
            for (int j = 0; j < path.size() - 1; j++) {
                restPath.add(path.get(j));
            }
            final Node<PrologAbstractState> last = path.get(path.size() - 1);
            final Node<PrologAbstractState> node = path.get(path.size() - 2);
            // case for backtrack substitution plus backtracking
            if (graph.isNoUnifyFailNode(node)
                || (graph.getLastChild(node).equals(last) && (graph.isNoUnifyCaseNode(node) || graph
                    .isUnequalsCaseNode(node))))
            {
                return RuleConstructor.compSkip(restPath, i + 1, graph, aborter);
            }
            // case for VAR_CASE
            // TODO
            // case for backtracking or cutting
            if (PrologGraphProcessor.isBacktracking(graph, node)
                || (graph.getLastChild(node).equals(last) && (graph.isBacktrackSecond(node)
                //|| graph.isVarCaseNode(node)
                ))
                || (i > 1 && graph.isCutNode(node)))
            {
                return RuleConstructor.compSkip(
                    restPath,
                    i + PrologGraphProcessor.getChange(graph, node, last),
                    graph,
                    aborter);
            }
            // case for introducing
            if (graph.isIntroducing(node)) {
                return RuleConstructor.compSkip(
                    restPath,
                    PrologGraphProcessor.getReduce(graph, node, last, i - 1) + 1,
                    graph,
                    aborter);
            }
            // for all other operations, just recurse!
            return RuleConstructor.compSkip(restPath, i, graph, aborter);
        }
        return i;
    }

}
