package aprove.verification.dpframework.PiDPProblem;

import java.util.*;
import java.util.concurrent.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PiDPProblem.AfsRefinementAlgorithm.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

public final class PPiDPProblem extends AbstractPiDPProblem {

    private final FunctionSymbol startSymbol;

    /**
     * creates a QDP-problem
     * @param P
     * @param rWithQ
     * @param graph - the graph should be the (P,Q,R) dependency graph
     */
    private PPiDPProblem(ImmutableSet<GeneralizedRule> P,
            AbstractPiTRSProblem rWithPi, PiDependencyGraph graph) {
        this(P, rWithPi, graph,
            rWithPi.getDPs().y.get(((PPiTRSProblem) rWithPi).getStartSymbol()));
    }

    private PPiDPProblem(ImmutableSet<GeneralizedRule> P,
            AbstractPiTRSProblem rWithPi, PiDependencyGraph graph,
            FunctionSymbol startSymbol) {
        super("PPiDP", "Partial-Pi-DP-Problem", P, rWithPi, graph);
        this.startSymbol = startSymbol;

    }

    public static PPiDPProblem create(ImmutableSet<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi) {
        if (Globals.useAssertions) {
            assert rWithPi instanceof PPiTRSProblem;
        }
        PiDependencyGraph graph = PiDependencyGraph.create(P, rWithPi);
        return new PPiDPProblem(P, rWithPi, graph);
    }

    public static PPiDPProblem create(ImmutableSet<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi,
        FunctionSymbol startSymbol) {
        if (Globals.useAssertions) {
            assert rWithPi instanceof PPiTRSProblem;
            assert CollectionUtils.getRootSymbols(P).contains(startSymbol);
        }
        PiDependencyGraph graph = PiDependencyGraph.create(P, rWithPi);
        return new PPiDPProblem(P, rWithPi, graph, startSymbol);
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer s = new StringBuffer();
        s.append(o.export("Partial Pi DP problem:"));
        s.append(o.cond_linebreak());
        if (this.getP().isEmpty()) {
            s.append("P is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS P consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getP(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getRwithPi().getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getRwithPi().getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getRwithPi().getPi().isEmpty()) {
            s.append("Pi is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The partial argument filtering Pi contains the following mapping:"));
            s.append(o.cond_linebreak());
            s.append(o.export(this.getRwithPi().getPi()));
            s.append(o.cond_linebreak());
        }

        s.append(o.export("We have to consider all (P,R,PPi)-chains"));

        return s.toString();
    }

    public FunctionSymbol getStartSymbol() {
        return this.startSymbol;
    }

    @Override
    protected AbstractPiDPProblem createProblem(ImmutableSet<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi,
        PiDependencyGraph graph) {
        return new PPiDPProblem(P, rWithPi, graph);
    }

    @Override
    protected Set<PPiDPProblem> getSubProblems(ImmutableSet<GeneralizedRule> P,
        PiDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert (graph.getP().equals(P));
            assert (this.getP().containsAll(P));
            assert (this.getP().size() != P.size());
        }

        Set<PPiDPProblem> subProblems = new LinkedHashSet<PPiDPProblem>();

        /* determine set of ``entry'' rules of this SCC */
        Set<GeneralizedRule> entryRules = new LinkedHashSet<GeneralizedRule>();
        for (GeneralizedRule rule : P) {
            ImmutableSet<GeneralizedRule> predecessors =
                this.getDependencyGraph().getPredecessors(rule);
            if (!P.containsAll(predecessors)
                || rule.getLeft().getRootSymbol().equals(this.startSymbol)) {
                entryRules.add(rule);
            }
        }

        Set<PiDependencyGraph> graphs;
        Set<GeneralizedRule> startRules;
        Set<TRSVariable> finiteVariables;
        Map<TRSVariable, Afs> f_0;
        Map<GeneralizedRule, Map<TRSVariable, Afs>> g_0, groundMapping;
        Afs newPi;
        PPiTRSProblem pitrs;
        /* for each entry node one sub-problem */
        for (GeneralizedRule entryRule : entryRules) {
            /* compute subgraph with all predecessors of this entry node */
            graphs = this.getPredecessorsGraphs(entryRule, P);

            /* for all predecessors graphs... */
            for (PiDependencyGraph g : graphs) {
                /* get all start nodes in this subgraph */
                startRules = this.getStartRules(g);

                /* for all start nodes... */
                for (GeneralizedRule startRule : startRules) {
                    /* detect finite variables in this start rule*/
                    finiteVariables = this.getPi().filterTerm(startRule.getLeft()).getVariables();
                    /* generate initial f_0 */
                    f_0 = new LinkedHashMap<TRSVariable, Afs>(finiteVariables.size());
                    for (TRSVariable v : finiteVariables) {
                        f_0.put(v, this.getPi());
                    }
                    /* generate initial f_0 */
                    g_0 = new LinkedHashMap<GeneralizedRule, Map<TRSVariable, Afs>>();
                    g_0.put(startRule, f_0);

                    /* ...compute ground mapping */
                    groundMapping = this.groundMapping(g, startRule, g_0);

                    /* and intersect filters */
                    newPi = this.computeAfsForTerm(entryRule.getLeft(), groundMapping.get(entryRule));

                    /* create new TRS problem with new filter and new start symbol */
                    pitrs = PPiTRSProblem.create(this.getR(), new ImmutableAfs(newPi), null);

                    /* add new DP problem */
                    subProblems.add(new PPiDPProblem(P, pitrs, graph,
                        entryRule.getLeft().getRootSymbol()));
                }
            }
        }

        /* make this a real set */
        Set<PPiDPProblem> realSubProblems = new LinkedHashSet<PPiDPProblem>();
        for(PPiDPProblem problem : subProblems) {
            boolean add = true;
            for(PPiDPProblem exProblem : realSubProblems) {
                if(exProblem.getPi().sameFilteringAs(problem.getPi())) {
                    add = false; break;
                }
            }
            if(add) {
                realSubProblems.add(problem);
            }
        }

        return realSubProblems;
    }

    /**
     * returns the same problem with a smaller argument filtering
     */
    @Override
    public AbstractPiDPProblem getSameProblem(ImmutableAfs Pi) {
        if (Globals.useAssertions) {
            assert Pi.isRefinementOf(this.getRwithPi().getPi()) == YNM.YES;
        }
        AbstractPiTRSProblem rWithPi =
            PPiTRSProblem.create(this.getRwithPi().getR(), Pi,
                ((PPiTRSProblem) this.getRwithPi()).getStartSymbol());
        return new PPiDPProblem(this.getP(), rWithPi,
            this.getDependencyGraph(), this.startSymbol);
    }

    /**
     * returns a subproblem with smaller R
     */
    @Override
    public AbstractPiDPProblem getSubProblemWithSmallerR(ImmutableSet<GeneralizedRule> R) {
        if (Globals.useAssertions) {
            assert (this.getRwithPi().getR().containsAll(R));
        }
        Set<FunctionSymbol> sig = CollectionUtils.getFunctionSymbols(R);
        sig.addAll(CollectionUtils.getFunctionSymbols(this.getP()));
        Afs newPi = this.getRwithPi().getPi().reduceToSignature(sig);
        AbstractPiTRSProblem pitrs =
            PPiTRSProblem.create(R, new ImmutableAfs(newPi),
                ((PPiTRSProblem) this.getRwithPi()).getStartSymbol());
        PiDependencyGraph subGraph =
            this.getDependencyGraph().getSubGraph(this.getP(), pitrs.getR());
        return new PPiDPProblem(this.getP(), pitrs, subGraph, this.startSymbol);
    }

    /*- private methods ------------------------------------------------------*/

    private TypeGraph tau = null;

    private TypeGraph getTypeGraph() {
        if (this.tau == null) {
            this.tau = new TypeGraph(this.getR());
        }
        return this.tau;
    }

    private Map<GeneralizedRule, Map<TRSVariable, Afs>> groundMapping(PiDependencyGraph g,
        GeneralizedRule rule_0,
        Map<GeneralizedRule, Map<TRSVariable, Afs>> g_0) {

        /* get successor rules */
        ImmutableSet<GeneralizedRule> succRules = g.getSuccessors(rule_0);
        if (succRules.size() == 0) {
            return g_0;
        }

        /* get usable rules in R and compute the corresponding type assignment */
        ImmutableSet<GeneralizedRule> usableRules =
            this.getUsableRulesFrom(rule_0);

        /* compute argument filter for rhs */
        ImmutableAfs pi =
            this.computeAfsForTerm(rule_0.getRight(), g_0.get(rule_0));

        /* use refinement algorithm to compute pi for usable rules */
        pi = this.refineFilterForUsableRules(pi, usableRules);

        /* for all successors i \in \{1, \ldots, n\} */
        ArrayList<Map<GeneralizedRule, Map<TRSVariable, Afs>>> g_is =
            new ArrayList<Map<GeneralizedRule, Map<TRSVariable, Afs>>>(
                succRules.size() + 1);
        g_is.add(g_0);
        int i = 1;
        Map<TRSVariable, Afs> f_i, f_i_prime, f_i_2prime;
        Map<GeneralizedRule, Map<TRSVariable, Afs>> g_i_prime;
        Set<TRSVariable> domCap;
        for (GeneralizedRule rule_i : succRules) {
            /* compute f_i */
            f_i = this.computeVariableMapping(rule_0, rule_i, g_0.get(rule_0), pi);

            /* compute g_i */
            g_i_prime = new LinkedHashMap<GeneralizedRule, Map<TRSVariable, Afs>>(g_is.get(i - 1));
            if (g_is.get(i - 1).containsKey(rule_i)) {
                f_i_prime = g_is.get(i - 1).get(rule_i);
                boolean recursionEnd =
                    f_i.keySet().containsAll(f_i_prime.keySet());
                if (recursionEnd) {
                    for (Map.Entry<TRSVariable, Afs> entry : f_i_prime.entrySet()) {
                        if (entry.getValue().isRefinementOf(
                            f_i.get(entry.getKey())) != YNM.YES) {
                            recursionEnd = false;
                            break;
                        }
                    }
                }

                if (recursionEnd) {
                    g_is.add(g_is.get(i - 1));
                } else {
                    f_i_2prime = new LinkedHashMap<TRSVariable, Afs>();
                    domCap = new LinkedHashSet<TRSVariable>(f_i.keySet());
                    domCap.retainAll(f_i_prime.keySet());
                    for (TRSVariable v : domCap) {
                        f_i_2prime.put(v, f_i.get(v).intersectWith(
                            f_i_prime.get(v)));
                    }

                    g_i_prime.put(rule_i, f_i_2prime);
                    g_is.add(this.groundMapping(g, rule_i, g_i_prime));
                }
            } else {
                g_i_prime.put(rule_i, f_i);
                g_is.add(this.groundMapping(g, rule_i, g_i_prime));
            }

            ++i;
        }

        /* return last mapping */
        return g_is.get(g_is.size() - 1);
    }

    private Set<PiDependencyGraph> getPredecessorsGraphs(GeneralizedRule entryNode,
        ImmutableSet<GeneralizedRule> scc) {
        Set<PiDependencyGraph> result = new LinkedHashSet<PiDependencyGraph>();
        /* get induced subgraph containing only predecessors of entry node */
        PiDependencyGraph predGraph = this.getPredecessorsGraph(entryNode, scc);

        /* to examin different paths to the entry node, sccs have to be considered on this path as well */
        SCCGraph<GeneralizedRule, Object> sccPredGraph =
            new DirectSCCGraph<GeneralizedRule, Object>(
                predGraph.getGraphStructure(), false);

        /* create an array of sets of predecessor rules */
        ArrayList<Set<GeneralizedRule>> allPredecessorPaths =
            new ArrayList<Set<GeneralizedRule>>();
        allPredecessorPaths.add(new LinkedHashSet<GeneralizedRule>());

        /* compute all paths */
        this.collectAllPredecessorRules(sccPredGraph,
            sccPredGraph.getSccNodeFromObject(entryNode), allPredecessorPaths,
            0);

        /* create sub graphs */
        for (Set<GeneralizedRule> rules : allPredecessorPaths) {
            result.add(this.getDependencyGraph().getSubGraphFromPRules(rules));
        }

        return result;
    }

    private PiDependencyGraph getPredecessorsGraph(GeneralizedRule entryNode,
        ImmutableSet<GeneralizedRule> scc) {
        Set<GeneralizedRule> allPredecessors =
            new LinkedHashSet<GeneralizedRule>();
        Queue<GeneralizedRule> queue =
            new LinkedBlockingQueue<GeneralizedRule>();
        queue.add(entryNode);
        ImmutableSet<GeneralizedRule> predecessors;
        while (!queue.isEmpty()) {
            GeneralizedRule rule = queue.poll();
            allPredecessors.add(rule);
            predecessors = this.getDependencyGraph().getPredecessors(rule);
            for (GeneralizedRule predecessor : predecessors) {
                if (!allPredecessors.contains(predecessor)
                    && !scc.contains(predecessor)) {
                    queue.add(predecessor);
                }
            }
        }
        return this.getDependencyGraph().getSubGraphFromPRules(allPredecessors);
    }

    private void collectAllPredecessorRules(SCCGraph<GeneralizedRule, Object> graph,
        Node<Cycle<GeneralizedRule>> node,
        ArrayList<Set<GeneralizedRule>> allPredecessors,
        int index) {

        if (!allPredecessors.get(index).contains(node)) {
            /* add all rules which are contained in this scc node */
            allPredecessors.get(index).addAll(node.getObject().getNodeObjects());

            /* get all predecessors of this node */
            Set<Node<Cycle<GeneralizedRule>>> predecessors = graph.getIn(node);

            /* go on recursivly */
            if (predecessors.size() >= 1) {
                /* split paths if size > 1, means copy current path */
                int lastIndex = allPredecessors.size() - 1;
                if (predecessors.size() > 1) {
                    Set<GeneralizedRule> newRules;
                    for (int i = 1; i < predecessors.size(); ++i) {
                        newRules = new LinkedHashSet<GeneralizedRule>(allPredecessors.get(index));
                        allPredecessors.add(newRules);
                    }
                }

                /* follow all paths backwards */
                int i = 0;
                for (Node<Cycle<GeneralizedRule>> predNode : predecessors) {
                    this.collectAllPredecessorRules(graph, predNode,
                        allPredecessors, i == 0 ? index : lastIndex + i);
                    i++;
                }
            }
        }
    }

    private Set<GeneralizedRule> getStartRules(PiDependencyGraph g) {
        Set<GeneralizedRule> startRules = new LinkedHashSet<GeneralizedRule>();

        ImmutableSet<GeneralizedRule> P = g.getP();
        for (GeneralizedRule rule : P) {
            if (rule.getRootSymbol().equals(this.getStartSymbol())) {
                startRules.add(rule);
            }
        }

        return startRules;
    }

    private ImmutableSet<GeneralizedRule> getUsableRulesFrom(GeneralizedRule pRule) {
        Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>();

        /* get rules */
        Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> R_map =
            this.getRwithPi().getRuleMap();
        /* get defined symbols */
        Set<FunctionSymbol> R_roots =
            new LinkedHashSet<FunctionSymbol>(R_map.size());
        for (FunctionSymbol f : R_map.keySet()) {
            R_roots.add(f);
        }
        Queue<FunctionSymbol> f_queue =
            new LinkedBlockingQueue<FunctionSymbol>();
        for (FunctionSymbol f : R_roots) { /* which defined symbols appear in rhs of predecessor rule? */
            if (pRule.getRight().getFunctionSymbols().contains(f)) {
                f_queue.add(f);
            }
        }

        /* add all rules into R and check if the rhs have again defined symbols */
        FunctionSymbol f;
        while (!f_queue.isEmpty()) {
            f = f_queue.poll();
            rules.addAll(R_map.get(f));
            R_roots.remove(f);
            for (GeneralizedRule rule : R_map.get(f)) {
                for (FunctionSymbol root_symbol : R_roots) {
                    if (rule.getRight().getFunctionSymbols().contains(
                        root_symbol)) {
                        f_queue.add(root_symbol);
                    }
                }
            }
        }

        return new ImmutableRuleSet<GeneralizedRule>(rules);
    }

    private ImmutableAfs computeAfsForTerm(TRSTerm term,
        Map<TRSVariable, Afs> finiteVariableMapping) {
        Afs newPi = new Afs();
        for (Map.Entry<TRSVariable, Afs> entry : finiteVariableMapping.entrySet()) {
            if (term.getVariables().contains(entry.getKey())) {
                newPi = newPi.intersectWith(entry.getValue());
            }
        }

        if (!term.isVariable()) {
            TRSFunctionApplication funcApp = (TRSFunctionApplication) term;

            /* initialize */
            newPi.removeFiltering(funcApp.getRootSymbol());

            /* get finite variables in the term */
            Set<TRSVariable> finiteVariables =
                new LinkedHashSet<TRSVariable>(funcApp.getVariables());
            finiteVariables.retainAll(finiteVariableMapping.keySet());

            /* get evil variables which have yet to be filtered */
            Set<TRSVariable> evilVariables =
                new LinkedHashSet<TRSVariable>(
                    newPi.filterTerm(funcApp).getVariables());
            evilVariables.removeAll(finiteVariables);

            /* get all variable+positions in the term */
            Map<TRSVariable, List<Position>> variablePositions =
                funcApp.getVariablePositions();

            /* find filtering for all evil Variables */
            RefinementHeuristic heuristic =
                new ImprovedTypeBasedRefinementHeuristic(this.getTypeGraph());
            Set<Pair<FunctionSymbol, Integer>> refinedPositions =
                new LinkedHashSet<Pair<FunctionSymbol, Integer>>();
            Pair<FunctionSymbol, Integer> refinePosition;
            for (TRSVariable evilVariable : evilVariables) {
                /* find filter */
                for (Position position : variablePositions.get(evilVariable)) {
                    if (newPi.filterPosition(funcApp, position) != YNM.NO) { /* nothing to do if position is already filtered away */
                        refinePosition =
                            heuristic.getSymbolArgumentToFilter(funcApp,
                                position); /* use refinement heuristic */
                        refinedPositions.add(refinePosition);
                        newPi.setFiltering(refinePosition.x,
                            refinePosition.y.intValue(), YNM.NO);
                    }
                }
            }

            /* try to remove unnecessary filtering */
            AfsRefinementAlgorithm.removeUnnecessaryFiltering(newPi, funcApp, evilVariables, refinedPositions);
        }

        return new ImmutableAfs(newPi);
    }

    private ImmutableAfs refineFilterForUsableRules(Afs pi,
        ImmutableSet<GeneralizedRule> usableRules) {
        TypeGraph tau = this.getTypeGraph();
        if (!usableRules.isEmpty()) {
            tau = new TypeGraph(usableRules);
        }
        pi = AfsRefinementAlgorithm.refineArgumentFilter(pi,
                new LinkedHashSet<GeneralizedRule>(), usableRules,
                new ImprovedTypeBasedRefinementHeuristic(tau));
        return new ImmutableAfs(pi);
    }

    private Map<TRSVariable, Afs> computeVariableMapping(GeneralizedRule rule,
        GeneralizedRule succRule,
        Map<TRSVariable, Afs> f_0,
        ImmutableAfs pi) {
        Map<TRSVariable, Afs> result = new LinkedHashMap<TRSVariable, Afs>();

        ImmutableSet<FunctionSymbol> definedSymbolsOfR =
            this.getRwithPi().getDefinedSymbolsOfR();

        Set<String> used = new LinkedHashSet<String>();
        for (TRSVariable v : rule.getVariables()) {
            used.add(v.getName());
        }
        for (TRSVariable v : succRule.getVariables()) {
            used.add(v.getName());
        }
        FreshNameGenerator fng =
            new FreshNameGenerator(used, new AppendNameGenerator(1, 2));
        TRSTerm capRhs = rule.getRight().tcap(definedSymbolsOfR, fng);

        Map<TRSVariable, List<Position>> lhsVariablePositions =
            succRule.getLeft().getVariablePositions();
        Set<TRSVariable> finiteVariables =
            pi.filterTerm(succRule.getLeft()).getVariables();

        Afs vPi, combinedPi;
        Position pos_prime;
        Set<TRSVariable> variables;
        for (TRSVariable v : finiteVariables) {
            vPi = new Afs(pi);

            for (Position pos : lhsVariablePositions.get(v)) {
                pos_prime = capRhs.getLongestPrefixInTerm(pos);
                variables = capRhs.getSubterm(pos_prime).getVariables();
                if (variables.isEmpty()) {
                    vPi = new Afs();
                    break;
                } else if (f_0.keySet().containsAll(
                    capRhs.getSubterm(pos_prime).getVariables())) {
                    combinedPi = new Afs();
                    for (TRSVariable var : variables) {
                        combinedPi = combinedPi.intersectWith(f_0.get(var));
                    }
                    if (vPi.isRefinementOf(combinedPi) == YNM.YES) {
                        vPi = combinedPi;
                    }
                }
            }

            result.put(v, vPi);
        }

        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
