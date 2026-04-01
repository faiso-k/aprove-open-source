package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.IntTRSPolynomialOrderProcessor.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.RankingRedPairProcessor.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author marinag
 * Graph with function symbols as nodes.
 * The edges are labeled by sets of rules, such that for each rule the root symbol of the lhs
 * is the start node and the root of rhs is the end node.
 */
public class ProblemGraph extends SimpleGraph<FunctionSymbol, Set<IGeneralizedRule>> {

    private Node<FunctionSymbol> startNode;

    public static ProblemGraph create(final Set<Edge<Set<IGeneralizedRule>, FunctionSymbol>> edges) {
        return new ProblemGraph(edges, null);
    }

    public static ProblemGraph create(final IRSwTProblem intTRS) {
        final ProblemGraph pg = ProblemGraph.create(intTRS.getRules(), intTRS.getStartTerm());

        return pg;
    }

    public ProblemGraph compress(final Collection<Node<FunctionSymbol>> nodesToKeep, final Abortion aborter) {
        final Map<FunctionSymbol, Node<FunctionSymbol>> fSyms = new HashMap<>();

        for (final Node<FunctionSymbol> node : nodesToKeep) {
            fSyms.put(node.getObject(), node);
        }

        final Set<IGeneralizedRule> rules = this.getAllRules();

        RuleCombiner combiner = new RuleCombiner(rules, fSyms.keySet(), aborter);
        Set<IGeneralizedRule> resRules = combiner.combineRules(true, true).y;

        resRules =
            TerminationSCCToIDPv1Processor.cleanConstraints(
                resRules,
                false,
                true,
                IDPPredefinedMap.DEFAULT_MAP,
                aborter);
        resRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(resRules, IDPPredefinedMap.DEFAULT_MAP);
        resRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(resRules, IDPPredefinedMap.DEFAULT_MAP);
        resRules = IRSwTFormatTransformer.makeLhsLinear(resRules, IDPPredefinedMap.DEFAULT_MAP);

        final SimpleGraph<FunctionSymbol, Set<IGeneralizedRule>> graph = new SimpleGraph<>();

        for (final IGeneralizedRule rule : rules) {

            for (final FunctionSymbol fSym : rule.getFunctionSymbols()) {
                if (!fSyms.containsKey(fSym)) {
                    fSyms.put(fSym, new Node<>(fSym));
                }
            }
        }

        for (final IGeneralizedRule rule : resRules) {
            if (!(rule.getRight() instanceof TRSFunctionApplication)
                || (rule.getCondTerm() != null && rule.getCondTerm().equals(ToolBox.buildFalse())))
            {
                continue;
            }

            final Node<FunctionSymbol> lfSymNode = fSyms.get(rule.getLeft().getRootSymbol());
            final Node<FunctionSymbol> rfSymNode = fSyms.get(((TRSFunctionApplication) rule.getRight()).getRootSymbol());

            Edge<Set<IGeneralizedRule>, FunctionSymbol> edge = graph.getEdge(lfSymNode, rfSymNode);

            if (edge == null) {
                graph.addEdge(lfSymNode, rfSymNode, new HashSet<IGeneralizedRule>());
                edge = graph.getEdge(lfSymNode, rfSymNode);
            }

            final Set<IGeneralizedRule> edgeRules = edge.getObject();
            edgeRules.add(rule);

            graph.replaceEdge(lfSymNode, rfSymNode, edgeRules);
        }

        return ProblemGraph.create(graph.getEdges());
    }

    public Node<FunctionSymbol> getStartNode() {
        return this.startNode;
    }

    private int createOrder(
        final Node<FunctionSymbol> node,
        final int order,
        final Map<Node<FunctionSymbol>, Integer> orderMap)
    {
        if (orderMap.containsKey(node)) {
            return order;
        }

        orderMap.put(node, order);

        int newOrder = order + 1;

        if (this.contains(node)) {

            for (final Node<FunctionSymbol> e : this.getOut(node)) {
                newOrder = this.createOrder(e, newOrder, orderMap);
            }
        }

        return newOrder;
    }

    private Map<Node<FunctionSymbol>, Integer> createOrder() {

        final Map<Node<FunctionSymbol>, Integer> orderMap = new HashMap<>();

        if (this.startNode != null) {
            this.createOrder(this.startNode, 0, orderMap);
        } else {
            int order = 0;

            for (final Node<FunctionSymbol> node : this.getNodes()) {
                orderMap.put(node, order++);
            }
        }

        return orderMap;
    }

    /**
     * @return
     */
    public List<Node<FunctionSymbol>> getCutPoints() {
        final Map<Node<FunctionSymbol>, Integer> order = this.createOrder();

        final List<Node<FunctionSymbol>> cutPoints = new ArrayList<>();
        for (final Node<FunctionSymbol> node : this.getNodes()) {
            if (!order.containsKey(node)) {
                continue;
            }

            for (final Node<FunctionSymbol> next : this.getOut(node)) {
                if (cutPoints.contains(next)) {
                    continue;
                }

                final int orderA = order.get(node);
                final int orderB = order.get(next);

                if (orderA >= orderB) {
                    int i = 0;
                    for (; i < cutPoints.size() && order.get(cutPoints.get(i)) > order.get(next); i++) {
                    }

                    cutPoints.add(i, next);
                }
            }
        }

        return cutPoints;
    }

    private ProblemGraph(
        final Set<Edge<Set<IGeneralizedRule>, FunctionSymbol>> edges,
        final Node<FunctionSymbol> startNode)
    {
        super(new HashSet<Node<FunctionSymbol>>(), edges);
        this.startNode = startNode;
    }

    public Set<TRSVariable> getUnchangedVariables() {
        assert this.getStartNode() != null;

        final Set<Integer> indices = new HashSet<>();

        final int len = this.getStartNode().getObject().getArity();
        for (int i = 0; i < len; i++) {
            indices.add(i);
        }

        for (final IGeneralizedRule rule : this.getAllRules()) {
            for (final int i : new HashSet<>(indices)) {
                if (!rule.getLeft().getArgument(i).equals(((TRSFunctionApplication) rule.getRight()).getArgument(i))) {
                    indices.remove(i);
                    continue;
                }

                boolean toRemove = false;

                for (int j = 0; j < ((TRSFunctionApplication) rule.getRight()).getArguments().size(); j++) {
                    if (i == j) {
                        continue;
                    }

                    if (((TRSFunctionApplication) rule.getRight())
                        .getArgument(j)
                        .getVariables()
                        .contains(rule.getLeft().getArgument(i)))
                    {
                        toRemove = true;
                        break;
                    }
                }

                if (toRemove) {
                    indices.remove(i);
                }
            }

            if (indices.isEmpty()) {
                break;
            }
        }

        final Set<TRSVariable> vars = new HashSet<>();

        for (final IGeneralizedRule rule : this.getAllRules()) {
            for (final int i : indices) {
                vars.add((TRSVariable) rule.getLeft().getArgument(i));
            }

            if (indices.isEmpty()) {
                break;
            }
        }

        return vars;
    }

    private static Set<IGeneralizedRule> normalizeRule(
        final IGeneralizedRule r,
        final int arity,
        final FreshNameGenerator ng)
        {
        final Set<IGeneralizedRule> result = new HashSet<>();

        if (!(r.getRight() instanceof TRSFunctionApplication)
            || TermTools.Function.isDefined(((TRSFunctionApplication) r.getRight()).getRootSymbol()))
        {
            return result;
        }

        IGeneralizedRule rule = r;

        TRSFunctionApplication lfApp = rule.getLeft();
        TRSFunctionApplication rfApp = (TRSFunctionApplication) rule.getRight();

        FunctionSymbol lSym = lfApp.getRootSymbol();
        FunctionSymbol rSym = rfApp.getRootSymbol();

        TRSTerm cond = rule.getCondTerm();

        // Get nicely enumerated variables
        final Map<TRSVariable, TRSVariable> replaceMap = new HashMap<>();
        for (int i = 0; i < lSym.getArity(); i++) {
            final TRSTerm arg = lfApp.getArgument(i);
            if ((arg instanceof TRSVariable) && !replaceMap.containsValue(arg)) {
                replaceMap.put((TRSVariable) arg, ProblemGraph.createVariable(i));
            } else if (arg instanceof TRSVariable) {
                cond = TermTools.buildAnd(cond, ToolBox.buildEq(arg, ProblemGraph.createVariable(i)));
            }
        }

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(replaceMap));

        lfApp = lfApp.applySubstitution(sigma);
        rfApp = rfApp.applySubstitution(sigma);
        cond = cond == null ? TermTools.TRUE : cond.applySubstitution(sigma);

        final ArrayList<TRSTerm> argl = new ArrayList<>();
        final ArrayList<TRSTerm> argr = new ArrayList<>();

        for (int i = 0; i < arity; i++) {
            if (i < lfApp.getArguments().size()) {
                argl.add(lfApp.getArgument(i));
            } else {
                argl.add(ProblemGraph.createVariable(i));
            }

            if (i < rfApp.getArguments().size()) {
                TRSTerm arg = rfApp.getArgument(i);

                // I have no idea what this is supposed to do, but the result is obviously incorrect.
                // Transforms f(x) -> g(x*x) to {f(x) -> g(x'), f(x) -> x*x}, which is not even a valid IRS.
                if (false && (arg instanceof TRSFunctionApplication)
                    && !TermTools.Function.isDefined(((TRSFunctionApplication) arg).getRootSymbol()))
                {
                    arg = TRSTerm.createVariable(ng.getFreshName("x", false));

                    final IGeneralizedRule subRule =
                        IGeneralizedRule.create(
                            r.getLeft(),
                            ((TRSFunctionApplication) r.getRight()).getArgument(i),
                            r.getCondTerm());
                    result.addAll(ProblemGraph.normalizeRule(subRule, arity, ng));
                }
                argr.add(arg);
            } else {
                argr.add(TRSTerm.createVariable(ng.getFreshName("x", false)));
            }
        }

        lSym = FunctionSymbol.create(lSym.getName(), arity);
        rSym = FunctionSymbol.create(rSym.getName(), arity);

        lfApp = TRSTerm.createFunctionApplication(lSym, ImmutableCreator.create(argl));
        rfApp = TRSTerm.createFunctionApplication(rSym, ImmutableCreator.create(argr));

        rule = IGeneralizedRule.create(lfApp, rfApp, cond);

        result.add(rule);

        return result;
        }

    private static TRSVariable createVariable(final int index) {
        return TRSTerm.createVariable("y" + index);
    }

    private static Set<IGeneralizedRule> createStartRules(
        final String startName,
        final TRSFunctionApplication startTerm,
        final FreshNameGenerator ng,
        final int arity)
        {
        final Set<IGeneralizedRule> result = new HashSet<>();

        TRSFunctionApplication rfApp = startTerm;
        FunctionSymbol rSym = rfApp.getRootSymbol();

        final ArrayList<TRSTerm> argl = new ArrayList<>();
        final ArrayList<TRSTerm> argr = new ArrayList<>();

        for (int i = 0; i < arity; i++) {
            argl.add(ProblemGraph.createVariable(i));
        }

        TRSTerm cond = TermTools.TRUE;

        // Get nicely enumerated variables
        final Map<TRSVariable, TRSVariable> replaceMap = new HashMap<>();
        for (int i = 0; i < rSym.getArity(); i++) {
            final TRSTerm arg = rfApp.getArgument(i);
            if ((arg instanceof TRSVariable) && !replaceMap.containsValue(arg)) {
                replaceMap.put((TRSVariable) arg, ProblemGraph.createVariable(i));
            } else {
                cond = TermTools.buildAnd(cond, ToolBox.buildEq(arg, ProblemGraph.createVariable(i)));
            }
        }

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(replaceMap));

        rfApp = rfApp.applySubstitution(sigma);

        final FunctionSymbol lSym = FunctionSymbol.create(startName, arity);
        final TRSFunctionApplication lfApp =
            TRSTerm.createFunctionApplication(lSym, ImmutableCreator.create(argl));

        for (int i = 0; i < arity; i++) {
            if (i < rfApp.getArguments().size()) {
                TRSTerm arg = rfApp.getArgument(i);


                if ((arg instanceof TRSFunctionApplication)
                    && !TermTools.Function.isDefined(((TRSFunctionApplication) arg).getRootSymbol()))
                {
                    result.addAll(ProblemGraph.createStartRules(startName, (TRSFunctionApplication) arg, ng, arity));
                    arg = TRSTerm.createVariable(ng.getFreshName("x", false));
                }

                argr.add(arg);
            } else {
                argr.add(TRSTerm.createVariable(ng.getFreshName("x", false)));
            }
        }

        rSym = FunctionSymbol.create(rSym.getName(), arity);

        rfApp = TRSTerm.createFunctionApplication(rSym, ImmutableCreator.create(argr));

        final IGeneralizedRule rule = IGeneralizedRule.create(lfApp, rfApp, cond);

        result.add(rule);

        return result;
        }

    public ProblemGraph getNormalizedProblem() {

        int arity = 0;
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

        final Set<IGeneralizedRule> rs = this.getAllRules();

        for (final IGeneralizedRule r : rs) {
            for (final FunctionSymbol fs : r.getFunctionSymbols()) {
                ng.lockName(fs.getName());

                if (TermTools.Function.isDefined(fs)) {
                    continue;
                }

                if (fs.getArity() > arity) {
                    arity = fs.getArity();
                }
            }
        }

        final Set<Edge<Set<IGeneralizedRule>, FunctionSymbol>> edges = new HashSet();

        for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : this.getEdges()) {
            edges.add(new Edge<>(edge.getStartNode(), edge.getEndNode(), this.normalizeRules(edge.getObject(), ng, arity)));
        }

        final ProblemGraph normalized = ProblemGraph.create(edges);
        normalized.startNode = this.startNode;
        return normalized;
    }

    private Set<IGeneralizedRule> normalizeRules(
        final Set<IGeneralizedRule> rs,
        final FreshNameGenerator ng,
        final int arity)
        {
        final Set<IGeneralizedRule> rules = new HashSet<>();

        for (final IGeneralizedRule r : rs) {
            rules.addAll(ProblemGraph.normalizeRule(r, arity, ng));
        }

        return rules;
        }

    public static ProblemGraph create(final Set<IGeneralizedRule> rs, final TRSFunctionApplication startTerm) {
        final String startName = null;
        final Set<IGeneralizedRule> rules = new HashSet<>();
        rules.addAll(rs);

        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);


        for (final IGeneralizedRule r : rs) {
            for (final FunctionSymbol fs : r.getFunctionSymbols()) {
                ng.lockName(fs.getName());
            }
        }

        final FunctionSymbol start =
            FunctionSymbol.create(ng.getFreshName("start", false), startTerm.getArguments().size());

        rules.addAll(ProblemGraph.createStartRules(start.getName(), startTerm, ng, startTerm.getArguments().size()));

        return ProblemGraph.create(rules, start);
    }

    public static ProblemGraph create(final Set<IGeneralizedRule> rules, final FunctionSymbol start) {
        final Map<FunctionSymbol, Node<FunctionSymbol>> fSyms = new HashMap<>();
        final SimpleGraph<FunctionSymbol, Set<IGeneralizedRule>> graph = new SimpleGraph<>();

        for (final IGeneralizedRule rule : rules) {

            for (final FunctionSymbol fSym : rule.getFunctionSymbols()) {
                if (!fSyms.containsKey(fSym)) {
                    fSyms.put(fSym, new Node<>(fSym));
                }
            }
        }

        for (final IGeneralizedRule rule : rules) {
            if (!(rule.getRight() instanceof TRSFunctionApplication)
                || (rule.getCondTerm() != null && rule.getCondTerm().equals(ToolBox.buildFalse())))
            {
                continue;
            }

            final Node<FunctionSymbol> lfSymNode = fSyms.get(rule.getLeft().getRootSymbol());
            final Node<FunctionSymbol> rfSymNode = fSyms.get(((TRSFunctionApplication) rule.getRight()).getRootSymbol());

            Edge<Set<IGeneralizedRule>, FunctionSymbol> edge = graph.getEdge(lfSymNode, rfSymNode);

            if (edge == null) {
                graph.addEdge(lfSymNode, rfSymNode, new HashSet<IGeneralizedRule>());
                edge = graph.getEdge(lfSymNode, rfSymNode);
            }

            final Set<IGeneralizedRule> edgeRules = edge.getObject();
            edgeRules.add(rule);

            graph.replaceEdge(lfSymNode, rfSymNode, edgeRules);
        }

        for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> e : graph.getEdges()) {
            final int k = 0;
            final boolean b = e.getObject().isEmpty();

        }

        Node<FunctionSymbol> startNode;

        if (start != null) {
            startNode = fSyms.get(start);
            final Set<Node<FunctionSymbol>> reachable = graph.determineReachableNodes(Arrays.asList(fSyms.get(start)));
            final Set<Node<FunctionSymbol>> toRemove = new HashSet<>();

            toRemove.addAll(graph.getNodes());

            toRemove.removeAll(reachable);

            for (final Node<FunctionSymbol> node : toRemove) {
                graph.removeNode(node);
            }
        } else {
            startNode = null;
        }

        return new ProblemGraph(graph.getEdges(), startNode);
    }

    private static Set<IGeneralizedRule> cleanConditions(final Set<IGeneralizedRule> rules, final int arity) {
        final List<TRSVariable> vars = new ArrayList<>();
        for (int i = 0; i < arity; i++) {
            vars.add(ProblemGraph.createVariable(i));
        }
        final Set<TRSVariable> unchangedVars = new HashSet<>(vars);
        for (final IGeneralizedRule r : rules) {
            final ImmutableList<TRSTerm> args = ((TRSFunctionApplication) r.getRight()).getArguments();
            for (int i = 0; i < arity; i++) {
                if (!unchangedVars.contains(vars.get(i))) {
                    continue;
                }
                if (!args.get(i).equals(vars.get(i))) {
                    unchangedVars.remove(vars.get(i));
                    continue;
                }
                for (int j = 0; j < arity; j++) {
                    if (i == j) {
                        continue;
                    }
                    if (((TRSFunctionApplication) r.getRight()).getArgument(j).getVariables().contains(vars.get(i))) {
                        unchangedVars.remove(vars.get(i));
                        break;
                    }
                }
            }
        }
        if (unchangedVars.isEmpty()) {
            return rules;
        }
        return ProblemGraph.cleanConditions(rules, unchangedVars);
    }

    public Set<IGeneralizedRule> getAllRules() {
        final Set<IGeneralizedRule> rules = new HashSet<>();
        for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : this.getEdges()) {
            rules.addAll(edge.getObject());
        }
        return rules;

    }

    public Set<IGeneralizedRule> getReducingRules(final Map<IGeneralizedRule, Set<Set<IGeneralizedRule>>> cycles) {
        final Set<IGeneralizedRule> rules = this.getAllRules();
        final Set<IGeneralizedRule> redRules = new HashSet<>();
        final Set<IGeneralizedRule> bRules = new HashSet<>();

        final PolynomialOrderArguments args = new PolynomialOrderArguments();

        final IntTRSPolynomialOrderProcessor proc = new IntTRSPolynomialOrderProcessor(args);

        final IRSwTProblem problem = new IRSwTProblem(ImmutableCreator.create(rules));
        final BasicObligationNode oblNode = new BasicObligationNode(problem);
        final Abortion aborter = AbortionFactory.create();
        final Result res = proc.process(oblNode.getBasicObligation(), oblNode, aborter, null);

        final IntTRSPoloRedPairProof proof =
            (res.getObligationChild() != null ? (IntTRSPoloRedPairProof) res.getObligationChild().getProof() : null);


        if (proof != null
            && proof.getDroppedRulesDueToBoundedness() != null
            && proof.getDroppedRulesDueToDecrease() != null)
        {
            assert problem.getRules().containsAll(proof.getDroppedRulesDueToBoundedness())
            && problem.getRules().containsAll(proof.getDroppedRulesDueToDecrease());



            final Set<IGeneralizedRule> decRaw = new HashSet<>();

            decRaw.addAll(proof.getDroppedRulesDueToDecrease());

            boolean noIncRules = true;
            for (final IGeneralizedRule r : problem.getRules()) {
                if (proof.getDroppedRulesDueToDecrease().contains(r)) {
                    continue;
                }

                final IGeneralizedRule ruleA = r;
                final VarPolynomial before = proof.getIntepretation().apply(ruleA.getLeft());
                final VarPolynomial after = proof.getIntepretation().apply((TRSFunctionApplication) ruleA.getRight());

                final VarPolynomial diff = after.minus(before);

                if (before.isConstant() && after.isConstant()) {
                    final SimplePolynomial poly = diff.getConstantPart();

                    if (poly.getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {
                        //redRules.add(r);
                        continue;
                    }
                }

                if (diff.isConstant()) {
                    final SimplePolynomial poly = diff.getConstantPart();

                    if (poly.getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {
                        decRaw.add(r);
                        continue;
                    }
                }

                if (diff.isConcrete() && diff.allNegative()) {
                    continue;
                }

                noIncRules = false;
            }

            for (final IGeneralizedRule rule : proof.getDroppedRulesDueToBoundedness()) {
                final IGeneralizedRule ruleA = rule;
                bRules.add(ruleA);
            }

            for (final IGeneralizedRule rule : decRaw) {
                final IGeneralizedRule ruleA = rule;

                final boolean selfLoop =
                    ruleA.getLeft().getRootSymbol().equals(((TRSFunctionApplication) ruleA.getRight()).getRootSymbol());

                if (bRules.contains(ruleA)) {
                    redRules.add(ruleA);
                } else if (noIncRules && !selfLoop && cycles.containsKey(ruleA)) {
                    boolean toSkip = false;
                    for (final Set<IGeneralizedRule> c : cycles.get(ruleA)) {
                        final HashSet<IGeneralizedRule> cycle = new HashSet<>(c);

                        if (!problem.getRules().containsAll(cycle)) {
                            continue;
                        }

                        cycle.retainAll(bRules);

                        if (cycle.isEmpty()) {
                            toSkip = true;
                            break;
                        }
                    }

                    if (toSkip) {
                        continue;
                    }

                    redRules.add(ruleA);
                }

            }
        }

        final Set<IGeneralizedRule> reducingRules = new HashSet<>();

        for (final IGeneralizedRule r : redRules) {
            final IGeneralizedRule renamed =
                ToolBox.renameVariablesInRule(r, new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS));

            for (final IGeneralizedRule p : rules) {
                if (ToolBox.renameVariablesInRule(p, new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS)).equals(
                    renamed))
                {
                    reducingRules.add(p);
                }
            }
        }

        return reducingRules;
    }

    public Set<IGeneralizedRule> getReducingRulesSimple() {
        final Set<IGeneralizedRule> rules = this.getAllRules();
        final Set<IGeneralizedRule> redRules = new HashSet<>();
        final Set<IGeneralizedRule> bRules = new HashSet<>();

        final Arguments args = new Arguments();
        final RankingRedPairProcessor proc = new RankingRedPairProcessor(args);

        final IRSwTProblem problem =
            new IRSwTProblem(ImmutableCreator.create(rules));

        final BasicObligationNode oblNode = new BasicObligationNode(problem);
        final Abortion aborter = AbortionFactory.create();
        final Result res = proc.process(oblNode.getBasicObligation(), oblNode, aborter, null);

        final RankingReductionPairProof proof =
            (res.getObligationChild() != null ? (RankingReductionPairProof) res.getObligationChild().getProof() : null);

        if (proof != null
            && proof.getDroppedRulesDueToBoundedness() != null
            && proof.getDroppedRulesDueToDecrease() != null)
        {
            redRules.addAll(proof.getDroppedRulesDueToBoundedness());
            redRules.retainAll(proof.getDroppedRulesDueToDecrease());
        }

        final Set<IGeneralizedRule> reducingRules = new HashSet<>();

        for (final IGeneralizedRule r : redRules) {
            final IGeneralizedRule renamed =
                ToolBox.renameVariablesInRule(r, new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS));

            for (final IGeneralizedRule p : rules) {
                if (ToolBox.renameVariablesInRule(p, new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS)).equals(
                    renamed))
                {
                    reducingRules.add(p);
                }
            }
        }

        return reducingRules;
    }

    private Map<IGeneralizedRule, Set<Set<IGeneralizedRule>>> getSimpleCycles() {
        return ProblemGraph.getSimpleCycles(this.getAllRules());
    }

    private static Map<IGeneralizedRule, Set<Set<IGeneralizedRule>>> getSimpleCycles(final Set<IGeneralizedRule> set) {
        final Map<FunctionSymbol, Set<IGeneralizedRule>> startSym = new HashMap<>();

        for (final IGeneralizedRule r : set) {
            final FunctionSymbol fSym = r.getLeft().getRootSymbol();

            if (!startSym.containsKey(fSym)) {
                startSym.put(fSym, new HashSet<IGeneralizedRule>());
            }

            startSym.get(fSym).add(r);
        }
        final Map<IGeneralizedRule, Set<Set<IGeneralizedRule>>> cycles = new HashMap<>();

        for (final IGeneralizedRule r : set) {
            if (r.getLeft().getRootSymbol().equals(((TRSFunctionApplication) r.getRight()).getRootSymbol())) {
                continue;
            }

            cycles.put(
                r,
                ProblemGraph.getSimpleCycles(((TRSFunctionApplication) r.getRight()).getRootSymbol(), startSym, Arrays.asList(r)));
        }

        return cycles;
    }

    /**
     * @param fSym
     * @param startSym
     * @param prefix
     * @return
     */
    private static Set<Set<IGeneralizedRule>> getSimpleCycles(
        final FunctionSymbol fSym,
        final Map<FunctionSymbol, Set<IGeneralizedRule>> startSym,
        final List<IGeneralizedRule> prefix)
        {
        final Set<Set<IGeneralizedRule>> result = new HashSet<>();

        if (prefix
            .get(0)
            .getLeft()
            .getRootSymbol()
            .equals(((TRSFunctionApplication) prefix.get(prefix.size() - 1).getRight()).getRootSymbol()))
        {
            result.add(new HashSet<>(prefix));
        }

        if (startSym.containsKey(fSym)) {
            for (final IGeneralizedRule r : startSym.get(fSym)) {
                if (!prefix.contains(r)) {
                    boolean toSkip = false;

                    for (final IGeneralizedRule p : prefix) {
                        if (p.getLeft().getRootSymbol().equals(fSym)) {
                            toSkip = true;
                            break;
                        }
                    }

                    if (toSkip) {
                        continue;
                    }

                    final List<IGeneralizedRule> newPrefix = new ArrayList<>(prefix);
                    newPrefix.add(r);
                    result.addAll(ProblemGraph.getSimpleCycles(
                        ((TRSFunctionApplication) r.getRight()).getRootSymbol(),
                        startSym,
                        newPrefix));
                }
            }
        }

        return result;
        }


    public void removeRules(final Set<IGeneralizedRule> toRemove) {
        for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : new HashSet<>(this.getEdges())) {
            edge.getObject().removeAll(toRemove);

            if (edge.getObject().isEmpty()) {
                this.removeEdge(edge);
            }
        }
    }

    @Override
    public ProblemGraph getSubGraph(final Set<Node<FunctionSymbol>> nodes) {
        return ProblemGraph.create(super.getSubGraph(nodes).getEdges());
    }

    public Set<ProblemGraph> getSCCProblems() {
        final Set<ProblemGraph> SCCs = new HashSet<>();

        for (final Cycle<FunctionSymbol> scc : this.getSCCs()) {
            SCCs.add(ProblemGraph.create(this.getSubGraph(scc).getEdges()));
        }

        return SCCs;
    }

    public Set<IGeneralizedRule> removeBoundedAndDecreasingRules(final Abortion aborter, final Set<TRSVariable> unchanged)
    {
        final Set<IGeneralizedRule> removed = new HashSet<>();

        removed.addAll(this.removeRules());

        removed.addAll(this.removeRulesSimple());

        if (!this.getSCCs().isEmpty()) {
            this.splitRules(false);

            removed.addAll(this.removeRules());

            Log.report("REM", "4");
        }

        return removed;
    }

    private static Set<IGeneralizedRule> cleanConditions(final Set<IGeneralizedRule> rs, final Set<TRSVariable> unchanged) {
        final Set<IGeneralizedRule> rules = ProblemGraph.splitRules(rs);

        final Map<TRSVariable, Set<Pair<IGeneralizedRule, TRSTerm>>> varToAtoms = new HashMap<>();

        for (final IGeneralizedRule r : rules) {
            try {
                for (final TRSTerm atom : TermTools.getAtomsWithNegation(r.getCondTerm())) {
                    for (final TRSVariable var : atom.getVariables()) {
                        if (unchanged.contains(var)) {
                            if (!varToAtoms.containsKey(var)) {
                                varToAtoms.put(var, new HashSet<Pair<IGeneralizedRule, TRSTerm>>());
                            }
                            varToAtoms.get(var).add(new Pair<>(r, atom));
                        }
                    }
                }
            } catch (final UnsupportedException e) {
                //
            }
        }

        final Map<IGeneralizedRule, Map<TRSTerm, TRSTerm>> toRemove =
            new HashMap<>();

            for (final Entry<TRSVariable, Set<Pair<IGeneralizedRule, TRSTerm>>> entry : varToAtoms.entrySet()) {

                if (entry.getValue().size() == 1) {
                    final Pair<IGeneralizedRule, TRSTerm> pair = entry.getValue().iterator().next();

                    if (!unchanged.containsAll(pair.y.getVariables())) {
                        continue;
                    }

                    if (!toRemove.containsKey(pair.x)) {
                        toRemove.put(pair.x, new HashMap<TRSTerm, TRSTerm>());
                    }

                    TRSTerm newT = TermTools.evaluate(pair.y);
                    newT = !TermTools.isFalse(newT) ? TermTools.TRUE : TermTools.FALSE;

                    toRemove.get(pair.x).put(pair.y, newT);
                }
            }

            final Set<IGeneralizedRule> result = new HashSet<>();

            for (final IGeneralizedRule r : rs) {
                if (toRemove.containsKey(r)) {

                    final Map<TRSTerm, TRSTerm> ruleMap = toRemove.get(r);

                    TRSTerm newCond = r.getCondTerm().replaceAll(ruleMap);
                    newCond = TermTools.evaluate(newCond);

                    if (TermTools.isFalse(newCond)) {
                        continue;
                    }

                    final IGeneralizedRule newRule =
                        IGeneralizedRule.create(r.getLeft(), r.getRight(), newCond);
                    result.add(newRule);
                } else {
                    result.add(r);
                }

            }

            return result;
    }


    private static Set<IGeneralizedRule> splitRules(final Set<IGeneralizedRule> rs) {
        final Set<IGeneralizedRule> rules = new HashSet<>();

        for (final IGeneralizedRule r : rs) {
            if (r.getCondTerm() == null) {
                rules.add(r);
            } else if (!TermTools.isFalse(r.getCondTerm())) {

                try {
                    final Collection<TRSTerm> dnf = TermTools.getDNFwNeq(r.getCondTerm());

                    for (final TRSTerm c : dnf)
                    {
                        if (TermTools.isFalse(c)) {
                            continue;
                        }

                        rules.add(IGeneralizedRule.create(r.getLeft(), r.getRight(), c));
                    }
                } catch (final UnsupportedException e) {
                    rules.add(IGeneralizedRule.create(r.getLeft(), r.getRight(), TermTools.TRUE));
                }
            }
        }

        return rules;

    }

    public Set<IGeneralizedRule> removeRules() {
        final Set<IGeneralizedRule> toRemove = new HashSet<>();

        final Stack<Pair<ProblemGraph, Map<IGeneralizedRule, Set<Set<IGeneralizedRule>>>>> termSCCs = new Stack<>();

        for (final ProblemGraph scc : this.getSCCProblems()) {
            termSCCs.push(new Pair<>(scc, scc.getSimpleCycles()));
        }

        while (!termSCCs.isEmpty()) {
            final Pair<ProblemGraph, Map<IGeneralizedRule, Set<Set<IGeneralizedRule>>>> pair = termSCCs.pop();
            final ProblemGraph subGraph = pair.x;

            final Set<IGeneralizedRule> redRules = subGraph.getReducingRules(pair.y);

            if (!redRules.isEmpty()) {
                toRemove.addAll(redRules);

                subGraph.removeRules(redRules);

                for (final ProblemGraph subSCC : subGraph.getSCCProblems()) {
                    termSCCs.push(new Pair<>(subSCC, /*pair.y)); //*/subSCC.getSimpleCycles()));
                }
            }
        }

        this.removeRules(toRemove);

        return toRemove;
    }

    public Set<IGeneralizedRule> removeRulesSimple() {
        final Set<IGeneralizedRule> toRemove = new HashSet<>();

        final Stack<ProblemGraph> termSCCs = new Stack<>();

        for (final ProblemGraph scc : this.getSCCProblems()) {
            termSCCs.push(scc);
        }

        while (!termSCCs.isEmpty()) {
            final ProblemGraph subGraph = termSCCs.pop();

            final Set<IGeneralizedRule> redRules = subGraph.getReducingRulesSimple();

            if (!redRules.isEmpty()) {
                toRemove.addAll(redRules);

                subGraph.removeRules(redRules);

                for (final ProblemGraph subSCC : subGraph.getSCCProblems()) {
                    termSCCs.push(subSCC);
                }
            }
        }

        this.removeRules(toRemove);

        return toRemove;
    }

    private void splitRules(final boolean keepNegatedAtoms) {
        for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : this.getEdges()) {
            final Set<IGeneralizedRule> rules = new HashSet<>();

            for (final IGeneralizedRule rule : edge.getObject()) {
                rules.addAll(ProblemGraph.splitRule(rule, keepNegatedAtoms));
            }

            this.replaceEdge(edge.getStartNode(), edge.getEndNode(), rules);

        }
    }

    private static Set<IGeneralizedRule> splitRule(
        final IGeneralizedRule rule, final boolean keepNegatedAtoms)
        {
        final Set<IGeneralizedRule> rules = new HashSet<>();

        if (rule.getCondTerm() == null) {
            rules.add(rule);
        } else if (!rule.getCondTerm().equals(ToolBox.buildFalse())) {


            try {
                final Collection<TRSTerm> dnf =
                    keepNegatedAtoms ? TermTools.getDNFwNeq(rule.getCondTerm()) : TermTools.getDNF(rule.getCondTerm());
                    for (final TRSTerm c : dnf)
                    {
                        if (TermTools.isFalse(c)) {
                            continue;
                        }

                        rules.add(IGeneralizedRule.create(rule.getLeft(), rule.getRight(), c));
                    }
            } catch (final UnsupportedException e) {
                rules.add(IGeneralizedRule.create(rule.getLeft(), rule.getRight(), TermTools.TRUE));
            }

        }

        return rules;
        }

    public IRSwTProblem toIntTRS() {
        final FunctionSymbol fSym = this.startNode == null ? null : this.startNode.getObject();
        TRSFunctionApplication fApp = null;

        final Set<IGeneralizedRule> rules = this.getAllRules();

        if (fSym != null) {
            for (final IGeneralizedRule r : new HashSet<>(rules)) {
                if (r.getLeft().getRootSymbol().equals(fSym)) {
                    rules.remove(r);
                    fApp = (TRSFunctionApplication) r.getRight();
                    break;
                }

            }
        }
        return new IRSwTProblem(ImmutableCreator.create(rules), fApp);
    }

    public ProgramGraph toProgramGraph() {
        final ProblemGraph norm = this.getNormalizedProblem();

        final Map<Node<FunctionSymbol>, Location> nodeToLoc = new HashMap<>();
        int id = 0;

        nodeToLoc.put(norm.getStartNode(), new Location(id++));

        final Set<Edge<TermTransitionPairsSet, LocationID>> edges = new HashSet<>();

        for (final Node<FunctionSymbol> l : norm.getNodes()) {
            if (!nodeToLoc.containsKey(l)) {
                nodeToLoc.put(l, new Location(id++));
            }

            final Location sLoc = nodeToLoc.get(l);
            for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> t : this.getOutEdges(l)) {
                final TermTransitionPairsSet trans = TermTransitionPairsSet.create(t.getObject());
                if (trans.getTransitionsPairs().isEmpty()) {
                    continue;
                }
                final Location d = nodeToLoc.get(t.getEndNode());
                if (!nodeToLoc.containsKey(t.getEndNode())) {
                    nodeToLoc.put(t.getEndNode(), new Location(id++));
                }
                final Location sChild = nodeToLoc.get(t.getEndNode());
                edges.add(new Edge<>(sLoc, sChild, trans));
            }
        }
        return new ProgramGraph(nodeToLoc.get(norm.getStartNode()), edges);
    }

    public Unwinding toUnwinding(final Collection<String> errorSymbols, final Abortion aborter) {

        final ProblemGraph norm = this.getNormalizedProblem();

        final Map<Node<FunctionSymbol>, Location> nodeToLoc = new HashMap<>();
        int id = 0;

        final Set<Edge<TermTransitionPairsSet, LocationID>> edges = new HashSet<>();

        final Node<FunctionSymbol> start = norm.getOut(norm.getStartNode()).iterator().next();
        nodeToLoc.put(start, new Location(id++));

        for (final Node<FunctionSymbol> l : norm.getNodes()) {
            if (norm.getStartNode().equals(l)) {
                continue;
            }

            if (!nodeToLoc.containsKey(l)) {
                if (errorSymbols.contains(l.getObject().getName())) {
                    nodeToLoc.put(l, new AbortLocation(id++));
                } else {
                    nodeToLoc.put(l, new Location(id++));
                }
            }

            final Location sLoc = nodeToLoc.get(l);
            for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> t : norm.getOutEdges(l)) {
                final TermTransitionPairsSet trans = TermTransitionPairsSet.create(t.getObject());
                if (trans.getTransitionsPairs().isEmpty()) {
                    continue;
                }
                final Location d = nodeToLoc.get(t.getEndNode());
                if (!nodeToLoc.containsKey(t.getEndNode())) {
                    if (errorSymbols.contains(t.getEndNode().getObject().getName())) {
                        nodeToLoc.put(t.getEndNode(), new AbortLocation(id++));
                    } else {
                        nodeToLoc.put(t.getEndNode(), new Location(id++));
                    }
                }
                final Location sChild = nodeToLoc.get(t.getEndNode());
                edges.add(new Edge<>(sLoc, sChild, trans));
            }
        }

        final ProgramGraph pg = new ProgramGraph(nodeToLoc.get(start), edges);

        return new Unwinding(pg, aborter);
    }

}
