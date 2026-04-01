package aprove.verification.dpframework.PiDPProblem;

import java.util.*;

import aprove.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class PiDependencyGraph implements Immutable {

    /*
     * real values
     */
    private final Graph<GeneralizedRule, Object> g;
    private final ImmutableSet<GeneralizedRule> R;
    private final ImmutableAfs Pi;

    /*
     * calculated values
     */
    private Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> rAsMap;  // a map from defined symbols to their rules
    private Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsRAsMap; // the lhs are in standard representation!!
                                                                     // this is essential for (t/i)cap!
    private Set<FunctionSymbol> defSymsOfR;
    private Set<Cycle<GeneralizedRule>> sccs; // the set of sccs of this graph, null if the graph itself is an SCC;
                                   // must be computed in the constructor

    /**
     * create Graph from scratch
     * @param P
     * @param rWithQ
     */
    private PiDependencyGraph(Set<GeneralizedRule> P,
            AbstractPiTRSProblem rWithPi) {
        this.R = rWithPi.getR();
        this.Pi = rWithPi.getPi();
        this.calculateDefSymbolsAndRuleMap();
        this.lhsRAsMap = GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(this.rAsMap);
        Set<Node<GeneralizedRule>> nodes = new LinkedHashSet<Node<GeneralizedRule>>();
        for (GeneralizedRule dp : P) {
            nodes.add(new Node<GeneralizedRule>(dp));
        }
        this.g = new Graph<GeneralizedRule, Object>(nodes);

        // iterate through all possible edges
        int n = nodes.size();
        Node<GeneralizedRule>[] nodeArr = new Node[n];
        nodeArr = nodes.toArray(nodeArr);
        for (int i = 0; i<n; i++) {
            Node<GeneralizedRule> fromDP = nodeArr[i];
            for (int j = i+1; j<n; j++) {
                Node<GeneralizedRule> toDP = nodeArr[j];
                // standard direction
                if (this.calculateConnection(fromDP, toDP)) {
                    this.g.addEdge(fromDP, toDP);
                }
                // reverse direction
                if (this.calculateConnection(toDP, fromDP)) {
                    this.g.addEdge(toDP, fromDP);
                }
            }
            // and self-cycle
            if (this.calculateConnection(fromDP, fromDP)) {
                this.g.addEdge(fromDP, fromDP);
            }
        }

        this.computeSccs();
    }

    private void calculateDefSymbolsAndRuleMap() {
        Map<FunctionSymbol, Set<GeneralizedRule>> ruleMap = new HashMap<FunctionSymbol, Set<GeneralizedRule>>();
        for (GeneralizedRule rule : this.R) {
            FunctionSymbol f = rule.getRootSymbol();
            Set<GeneralizedRule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<GeneralizedRule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> immutableMap = new HashMap<FunctionSymbol, ImmutableSet<GeneralizedRule>>();
        for (Map.Entry<FunctionSymbol, Set<GeneralizedRule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.rAsMap = ImmutableCreator.create(immutableMap);
        this.defSymsOfR = ImmutableCreator.create(immutableMap.keySet());
    }


    /**
     * create graph where P is a subset of the nodes in superGraph
     * => we do not have to check edges again
     * @param P
     * @param superGraph
     */
    private PiDependencyGraph(Set<Node<GeneralizedRule>> P, PiDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert(superGraph.g.getNodes().containsAll(P));
        }
        this.g = superGraph.g.getSubGraph(P);
        this.defSymsOfR = superGraph.defSymsOfR;
        this.lhsRAsMap = superGraph.lhsRAsMap;
        this.rAsMap = superGraph.rAsMap;
        this.R = superGraph.R;
        this.Pi = superGraph.Pi;
        this.computeSccs();
    }

    /**
     * create graph where P is a subset of the nodes in superGraph and
     * the edges are guaranteed to be included in the superGraph,
     * i.e. only existent edges may be deleted.
     * @param P
     * @param superGraph
     */
    private PiDependencyGraph(Set<Node<GeneralizedRule>> P, ImmutableSet<GeneralizedRule> R, PiDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert(superGraph.g.getNodes().containsAll(P));
        }
        this.R = R;
        this.Pi = superGraph.Pi;
        this.calculateDefSymbolsAndRuleMap();
        this.lhsRAsMap = GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(this.rAsMap);

        // create graph with corresponding node-set
        Graph<GeneralizedRule, Object> g = new Graph<GeneralizedRule, Object>(P);

        // now check all edges
        for (Edge<Object, GeneralizedRule> edge : superGraph.g.getEdges()) {
            Node<GeneralizedRule> from = edge.getStartNode();
            Node<GeneralizedRule> to   = edge.getEndNode();
            if (this.calculateConnection(from, to)) {
                g.addEdge(from, to);
            }
        }

        this.g = g;

        this.computeSccs();
    }

    public Graph<GeneralizedRule, Object> getGraphStructure() {
        return this.g;
    }

    public PiDependencyGraph getSubGraph(Set<Node<GeneralizedRule>> P) {
        return new PiDependencyGraph(P, this);
    }

    public PiDependencyGraph getSubGraphFromPRules(Set<GeneralizedRule> P) {
        Set<Node<GeneralizedRule>> nodesForP = this.g.getNodesFromObjects(P);
        return new PiDependencyGraph(nodesForP, this);
    }

    public PiDependencyGraph getSubGraph(Set<GeneralizedRule> P, ImmutableSet<GeneralizedRule> R) {
        Set<Node<GeneralizedRule>> nodesForP = this.g.getNodesFromObjects(P);
        return new PiDependencyGraph(nodesForP, R, this);
    }

    public static PiDependencyGraph create(Set<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi) {
        return new PiDependencyGraph(P, rWithPi);
    }

    private boolean calculateConnection(Node<GeneralizedRule> from, Node<GeneralizedRule> to) {
        GeneralizedRule s_to_t = from.getObject().getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        TRSTerm s = s_to_t.getLeft();
        TRSTerm t = s_to_t.getRight();
        TRSFunctionApplication u = to.getObject().getLhsInStandardRepresentation();
        if (t.isVariable()) {
            return true;
        }
        TRSFunctionApplication t_ = (TRSFunctionApplication) t;
        FunctionSymbol rootT = t_.getRootSymbol();

        // fast check before calculating cap
        if (!u.getRootSymbol().equals(rootT)) {
            if (!this.defSymsOfR.contains(rootT)) {
                return false;
            }
        }

        // okay, now do IEDG check
        TRSTerm cap_t = null;
        //@TODO Improve by using \pi-unifying icap
        cap_t = t.tcap(this.lhsRAsMap);

        //@TODO Improve by giving finite vars
        if (!cap_t.unifiesRational(u, new HashSet<TRSVariable>()).x) {
            return false;
        }
        return true;
    }

    private void computeSccs() {
        Set<Cycle<GeneralizedRule>> sccs = this.g.getSCCs();
        if (sccs.size() == 1) {
            if (sccs.iterator().next().size() == this.g.getNodes().size()) {
                this.sccs = null;
                return;
            }
        }
        this.sccs = sccs;
    }

    public boolean isSCC() {
        return this.sccs == null;
    }

    public ImmutableSet<PiDependencyGraph> getSubSCCs() {
        Set<PiDependencyGraph> subSccs = new LinkedHashSet<PiDependencyGraph>();
        for (Set<Node<GeneralizedRule>> scc : this.sccs) {
            subSccs.add(this.getSubGraph(scc));
        }
        return ImmutableCreator.create(subSccs);
    }

    public ImmutableSet<GeneralizedRule> getP() {
        return ImmutableCreator.create(this.g.getNodeObjects());
    }

    public String toDOT() {
        return this.g.toDOT(false);
    }

    public ImmutableSet<GeneralizedRule> getPredecessors(GeneralizedRule rule) {
        if (Globals.useAssertions) {
            assert this.getP().contains(rule);
        }
        Node<GeneralizedRule> dest = this.g.getNodeFromObject(rule);
        Set<Node<GeneralizedRule>> inNodes = this.g.getIn(dest);
        return new ImmutableRuleSet<GeneralizedRule>(
            this.g.getObjectsFromNodes(inNodes));
    }

    public ImmutableSet<GeneralizedRule> getSuccessors(GeneralizedRule rule) {
        if (Globals.useAssertions) {
            assert this.getP().contains(rule);
        }
        Node<GeneralizedRule> src = this.g.getNodeFromObject(rule);
        Set<Node<GeneralizedRule>> outNodes = this.g.getOut(src);
        return new ImmutableRuleSet<GeneralizedRule>(
            this.g.getObjectsFromNodes(outNodes));
    }
}
