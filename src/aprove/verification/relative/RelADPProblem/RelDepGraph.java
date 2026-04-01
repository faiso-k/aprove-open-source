package aprove.verification.relative.RelADPProblem;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Mostly just a wrapper for @see aprove.verification.dpframework.DPProblem.RelDepGraph
 * Additionally we store a set of relative rules to keep track of marked nodes
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelDepGraph implements Immutable {

    // ================================================================================
    // Attributes
    // ================================================================================
    
    /*
     * real values
     */
    private final Graph<Rule, ?> g;
    private final QUsableRules capCalculator;
    
    private final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap;
    
    private final Set<Rule> P_abs;
    private final Set<Rule> P_rel;
    
    /*
     * calculated values
     */
    private final QTermSet Q;
    private final boolean QsuperR;
    private final Set<Cycle<Rule>> sccs;


    /**
     * create Graph from scratch, if P is given, or start with "graph", if graph is given.
     * @param P - a set of DPs
     * @param graph a graph over DPs
     * @param rWithQ
     */
    private RelDepGraph(Set<Rule> P_abs, Set<Rule> P_rel, QTRSProblem rWithQ, Graph<Rule,?> graph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        
        Set<Rule> P = new HashSet<>();
        P.addAll(P_abs);
        P.addAll(P_rel);
        
        if (Globals.useAssertions) {
            assert ((P == null) == (graph != null)); // exactly one of graph and P must be given
        }
        this.P_abs = P_abs;
        this.P_rel = P_rel;
        this.Q = rWithQ.getQ();
        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.QsuperR = rWithQ.QsupersetOfLhsR();
        
        this.annoMap = annoMap;

        final Set<FunctionSymbol> defsOfR = annoMap.getLRMap().keySet();
        
        if (graph == null) {
            int n = P.size();
            Set<Node<Rule>> nodes = new LinkedHashSet<Node<Rule>>(n);
            for (Rule dp : P) {
                nodes.add(new Node<Rule>(dp));
            }
            this.g = new Graph<Rule, Object>(nodes);

            // iterate through all possible edges
            Node<Rule>[] nodeArr = new Node[n];
            nodeArr = nodes.toArray(nodeArr);

            // first do crude approximation on root symbols
            // (only check nodes in sccs in more detail!)
            for (int i = 0; i<n; i++) {
                Node<Rule> fromDP = nodeArr[i];
                Rule fromDPRule = fromDP.getObject();
                //If the rule contains an annotation...
                if(fromDPRule.getRight().countAnnos(annoMap.getRLMap().keySet()) >= 0) {
                    for (int j = i+1; j<n; j++) {
                        Node<Rule> toDP = nodeArr[j];
                        Rule toDPRule = toDP.getObject();
                        // standard direction
                        if (this.calculateFastConnection(fromDPRule, toDPRule, defsOfR)) {
                            this.g.addEdge(fromDP, toDP);
                        }
                        // reverse direction
                        if (this.calculateFastConnection(toDPRule, fromDPRule, defsOfR)) {
                            this.g.addEdge(toDP, fromDP);
                        }
                    }
                    // and self-cycle
                    if (this.calculateFastConnection(fromDPRule, fromDPRule, defsOfR)) {
                        this.g.addEdge(fromDP, fromDP);
                    }
                }
            }
        } else {
            // we have a given graph, but of course we have to check whether we can
            // delete additional edges
            this.g = graph;
            Set<Pair<Node<Rule>,Node<Rule>>> delete = new LinkedHashSet<Pair<Node<Rule>,Node<Rule>>>();
            for (Edge<?,Rule> edge : this.g.getEdges()) {
                Node<Rule> start = edge.getStartNode();
                Node<Rule> end   = edge.getEndNode();
                if (!this.calculateFastConnection(start.getObject(), end.getObject(), defsOfR)) {
                    delete.add(new Pair<Node<Rule>, Node<Rule>>(start, end));
                }
            }
            // now update graph
            for (Pair<Node<Rule>, Node<Rule>> edge : delete) {
                this.g.removeEdge(edge.x, edge.y);
            }
        }

        Set<Cycle<Rule>> sccs = this.checkEdgesOnSccs(this.computeSccs());
        this.sccs = sccs;
    }

    /**
     * create graph where P is a subset of the nodes in superGraph
     * => we do not have to check edges again
     * @param P
     * @param superGraph
     */
    private RelDepGraph(Set<Node<Rule>> P, RelDepGraph superGraph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        if (Globals.useAssertions) {
            assert(superGraph.g.getNodes().containsAll(P));
        }
        Set<Rule> newPAbs = new HashSet<>();
        for(Node<Rule> node : P) {
            if(superGraph.P_abs.contains(node.getObject())) {
                newPAbs.add(node.getObject());
            }
        }
        this.P_abs = newPAbs;
        Set<Rule> newPRel = new HashSet<>();
        for(Node<Rule> node : P) {
            if(superGraph.P_rel.contains(node.getObject())) {
                newPRel.add(node.getObject());
            }
        }
        this.P_rel = newPRel;
        this.capCalculator = superGraph.capCalculator;
        this.g = superGraph.g.getSubGraph(P);
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;

        this.annoMap = annoMap;

        this.sccs = this.computeSccs();
    }

    /**
     * creates a DP-Graph from a given (fully evaluated graph) P and
     * the super DP-graph which contains the underlying TRS.
     * This constructor is intended for DP-transformations.
     * @param P
     * @param superGraph
     */
    private RelDepGraph(Graph<Rule, ?> P, RelDepGraph superGraph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        Set<Rule> newPAbs = new HashSet<>();
        for(Node<Rule> node : P.getNodes()) {
            if(superGraph.P_abs.contains(node.getObject())) {
                newPAbs.add(node.getObject());
            }
        }
        this.P_abs = newPAbs;
        Set<Rule> newPRel = new HashSet<>();
        for(Node<Rule> node : P.getNodes()) {
            if(superGraph.P_rel.contains(node.getObject())) {
                newPRel.add(node.getObject());
            }
        }
        this.P_rel = newPRel;
        this.capCalculator = superGraph.capCalculator;
        this.g = P;
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;

        this.annoMap = annoMap;

        this.sccs = this.computeSccs();
    }

    /**
     * creates a DP-Graph from a given DP-graph superGraph
     * and a collection of edges that should be dropped in the new graph.
     * @param P
     * @param superGraph
     */
    private RelDepGraph(Collection<Pair<Node<Rule>, Node<Rule>>> dropTheseEdges, RelDepGraph superGraph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        this.P_abs = superGraph.P_abs;
        this.P_rel = superGraph.P_rel;
        this.capCalculator = superGraph.capCalculator;
        this.g = superGraph.g.getCopy();
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;

        // now delete edges
        for (Pair<Node<Rule>, Node<Rule>> edge : dropTheseEdges) {
            Node<Rule> from = edge.x;
            Node<Rule> to = edge.y;
            this.g.removeEdge(from, to);
        }

        this.annoMap = annoMap;

        this.sccs = this.computeSccs();
    }


    /**
     * create graph where P is a subset of the nodes in superGraph and
     * the edges are guaranteed to be included in the superGraph,
     * i.e. only existent edges may be deleted.
     * @param P
     * @param superGraph
     */
    private RelDepGraph(Set<Node<Rule>> P, QTRSProblem rWithQ, RelDepGraph superGraph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        if (Globals.useAssertions) {
            assert(superGraph.g.getNodes().containsAll(P));
        }
        Set<Rule> newPAbs = new HashSet<>();
        for(Node<Rule> node : P) {
            if(superGraph.P_abs.contains(node.getObject())) {
                newPAbs.add(node.getObject());
            }
        }
        this.P_abs = newPAbs;
        Set<Rule> newPRel = new HashSet<>();
        for(Node<Rule> node : P) {
            if(superGraph.P_rel.contains(node.getObject())) {
                newPRel.add(node.getObject());
            }
        }
        this.P_rel = newPRel;
        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.Q = rWithQ.getQ();
        this.QsuperR = rWithQ.QsupersetOfLhsR();

        this.annoMap = annoMap;

        // create graph with corresponding node-set
        this.g = superGraph.g.getSubGraph(P);
        this.sccs = this.checkEdgesOnSccs(this.computeSccs());
    }

    /**
     * create a new QTRSProblem where rWithQ are the usable rules and the supProblem satisfies QsuperR.
     * Then the edges in the graph remain identical.
     * @param rWithQ
     * @param superGraph
     */
    private RelDepGraph(QTRSProblem rWithQ, RelDepGraph superGraph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        assert(superGraph.QsuperR);
        this.P_abs = superGraph.P_abs;
        this.P_rel = superGraph.P_rel;
        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.Q = rWithQ.getQ();
        this.QsuperR = rWithQ.QsupersetOfLhsR();

        this.annoMap = annoMap;

        // create graph with corresponding node-set
        Graph<Rule, ?> supGraph = superGraph.g;
        this.g = supGraph.getSubGraph(supGraph.getNodes());

        this.sccs = null;
    }

    public static RelDepGraph
        create(Set<Rule> p_abs, Set<Rule> p_rel, QTRSProblem withQ, Graph<Rule,?> graph, BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        return new RelDepGraph(p_abs, p_rel, withQ, graph, annoMap);
    }

    /**
     * creates a new DP-graph from this one by dropping a set of edges.
     * @param dropTheseEdges
     * @return
     */
    public RelDepGraph getSubGraphByDroppingEdges(Collection<Pair<Node<Rule>, Node<Rule>>> dropTheseEdges) {
        return new RelDepGraph(dropTheseEdges, this, this.annoMap);
    }

    public RelDepGraph getSubGraph(Set<Node<Rule>> P) {
        return new RelDepGraph(P, this, this.annoMap);
    }

    public RelDepGraph getSubGraphFromPRules(Set<Rule> P) {
        Set<Node<Rule>> nodesForP = this.g.getNodesFromObjects(P);
        return new RelDepGraph(nodesForP, this, this.annoMap);
    }

    /**
     * creates a graph where P is a subset of the nodes and we draw edges
     * according to a new rWithQ
     */
    public RelDepGraph getSubGraph(Set<Rule> P, QTRSProblem rWithQ) {
        Set<Node<Rule>> nodesForP = this.g.getNodesFromObjects(P);
        return new RelDepGraph(nodesForP, rWithQ, this, this.annoMap);
    }

    /**
     * creates a graph where P is a subset of the nodes and we draw edges
     * according to a new rWithQ
     */
    public RelDepGraph getSubGraph2(Set<Rule> P) {
        Set<Node<Rule>> nodesForP = this.g.getNodesFromObjects(P);
        return new RelDepGraph(nodesForP, this, this.annoMap);
    }

    /**
     * returns the graph where we restrict R to the usableRules.
     * Here, this problem has to be innermost.
     * @param rWithQ
     * @return
     */
    public RelDepGraph getUsableRulesSubGraph(QTRSProblem rWithQ) {
        return new RelDepGraph(rWithQ, this, this.annoMap);
    }
    
    public Set<Rule> getPAbs(){
        return P_abs;
    }
    
    public Set<Rule> getPRel(){
        return P_rel;
    }


    /**
     * only checks on outermost symbols
     * @param from
     * @param to
     * @param defSymsOfR - the defined symbols of R.
     * @return false, if there is no edge
     */
    private boolean calculateFastConnection(Rule from, Rule to, Set<FunctionSymbol> defSymsOfR) {
        Set<TRSFunctionApplication> tSet = from.getRight().getAnnoSubterms(this.annoMap.getRLMap());
        for(TRSFunctionApplication t : tSet) {
            final FunctionSymbol f = t.getRootSymbol();
            final FunctionSymbol g = annoMap.getLRMap().get(to.getRootSymbol());
            if(f.equals(g))
                return true;
        }
        return false;
    }

    /**
     * does the usual forward checks with T/ICap
     * @param from
     * @param to
     * @return false, if the edge can be deleted
     */
    private boolean calculateConnection(Rule from, Rule to) {
        Set<TRSFunctionApplication> tSet = from.getRight().getAnnoSubterms(this.annoMap.getRLMap());
        for(TRSFunctionApplication t : tSet) {
            Rule ruleWithDepSubterm = Rule.create(from.getLeft(), t);
            GeneralizedRule capped_s_to_t = this.capCalculator.getCappedDP(ruleWithDepSubterm);
            final TRSTerm cap_t = capped_s_to_t.getRight();
            if (Globals.useAssertions) {
                for (TRSVariable v : capped_s_to_t.getVariables()) {
                    assert (v.getName().startsWith(TRSTerm.SECOND_STANDARD_PREFIX) || v.getName().startsWith(TRSTerm.THIRD_STANDARD_PREFIX));
                }
            }
    
            final TRSFunctionApplication u = to.getLhsInStandardRepresentation().renameAtMap(Position.EPSILON, annoMap.getLRMap());
    
            final TRSSubstitution sigma = cap_t.getMGU(u);
    
            if (sigma == null) {
                
            } else if (!this.Q.isEmpty()) {
                // no normal form conditions in Q = empty case
    
                // check normal form condition u sigma
                final TRSTerm u_sigma = u.applySubstitution(sigma);
                if (!this.Q.canBeRewritten(u_sigma)) {
    
                    TRSTerm s = capped_s_to_t.getLeft();
    
                    // check normal form condition s sigma
                    final TRSTerm s_sigma = this.QsuperR ? s.applySubstitution(sigma) : s;
                    // s = s sigma in termination case
                    if (!this.Q.canBeRewritten(s_sigma)) {
                        return true;
                    }
                }
            } else {
                return true;
            }
        }
        return false;
    }

    /**
     * does the star check. Either Q super R has to be true or the TRS must be non-collapsing
     * @param from
     * @param to
     * @return false, if edge can be deleted;
     */
    private boolean calculateStarConnection(Rule from, Rule to) {
        if (Options.certifier.isRainbow())
         {
            return true; // currently not supported by rainbow
        }
        

        Set<TRSFunctionApplication> tSet = from.getRight().getAnnoSubterms(this.annoMap.getRLMap());
        for(TRSFunctionApplication depTerm : tSet) {
            Rule ruleWithDepSubterm = Rule.create(from.getLeft(), depTerm);
            Rule toRuleWithAnno = Rule.create(to.getLeft().renameAtMap(Position.EPSILON, annoMap.getLRMap()), to.getRight());
            
            final TRSTerm cap_u;
        
            if (this.QsuperR) {
                cap_u = this.capCalculator.getCapUsedRminusOneOfU(ruleWithDepSubterm, toRuleWithAnno);
            } else {
                if (Globals.useAssertions) {
                    assert(!this.capCalculator.getUnderlyingQTRS().isCollapsing());
                }
                cap_u = this.capCalculator.getCapRminusOneOfU(toRuleWithAnno);
            }
        
            final TRSTerm t = ruleWithDepSubterm.getRhsInStandardRepresentation();
        
            final TRSSubstitution sigma = t.getMGU(cap_u);
        
            if (sigma == null) {
                
            } else if (!cap_u.isVariable() && !this.Q.isEmpty()) {
                // do some Q-normal checks (if cap_u is variable, then we do not change anything, and s in Q-NF has been checked before
        
                final TRSTerm sSigma = ruleWithDepSubterm.getLhsInStandardRepresentation().applySubstitution(sigma);
                if (!this.Q.canBeRewritten(sSigma)) {
                    return true;
                }
            } else {
                return true;
            }
        }
        return false;
    }

    private Set<Cycle<Rule>> computeSccs() {
        // Rainbow, CeTA and CPF demand that all nodes be present in the decomposition,
        // even those that do not belong to any SCC.
        // Set<Cycle<Rule>> sccs = this.g.getSCCs(false);
        Set<Cycle<Rule>> sccs = this.g
                .getSCCs(!((Options.certifier.isRainbow()
                        || Options.certifier.isCeta()
                        || Options.certifier.isA3pat() || Options.certifier
                        .isCpf())));
        if (sccs.size() == 1) {
            if (sccs.iterator().next().size() == this.g.getNodes().size()) {
                return null;
            }
        }
        return sccs;
    }

    /**
     * Computes a finer connection on edges on sccs.
     */
    private Set<Cycle<Rule>> checkEdgesOnSccs(Set<Cycle<Rule>> localSccs) {
        List<Edge<?, Rule>> edges = new ArrayList<Edge<?, Rule>>(this.g.getEdges());
        boolean changed = false;
        if (localSccs == null) {
            for (Edge<?, Rule> e : edges) {
                Node<Rule> from = e.getStartNode();
                Node<Rule> to = e.getEndNode();
                if (!this.calculateConnection(from.getObject(), to.getObject())) {
                    this.g.removeEdge(from, to);
                    changed = true;
                }
            }
        } else {
            Map<Node<Rule>, Cycle<Rule>> nodeToScc = new HashMap<Node<Rule>, Cycle<Rule>>(this.g.getNodes().size());
            for (Cycle<Rule> cycle : localSccs) {
                for (Node<Rule> node : cycle) {
                    nodeToScc.put(node, cycle);
                }
            }

            for (Edge<?, Rule> e : edges) {
                Node<Rule> from = e.getStartNode();
                Node<Rule> to = e.getEndNode();
                Cycle<Rule> fromCycle = nodeToScc.get(from);
                if (fromCycle != null && fromCycle == nodeToScc.get(to)) {
                    if (!this.calculateConnection(from.getObject(), to.getObject())) {
                        this.g.removeEdge(from, to);
                        changed = true;
                    }
                }
            }
        }

        if (changed) {
            localSccs = this.computeSccs();
        }

        // now check *-graph conditions
        QTRSProblem qtrs = this.capCalculator.getUnderlyingQTRS();
        if (this.QsuperR
                || !qtrs.isCollapsing()) {
            // in termination case there is no chance if we have collapsing rules to delete further edges
            edges = new ArrayList<Edge<?, Rule>>(this.g.getEdges());
            changed = false;
            if (localSccs == null) {
                for (Edge<?, Rule> e : edges) {
                    Node<Rule> from = e.getStartNode();
                    Node<Rule> to = e.getEndNode();
                    if (!this.calculateStarConnection(from.getObject(), to.getObject())) {
                        this.g.removeEdge(from, to);
                        changed = true;
                    }
                }
            } else {
                Map<Node<Rule>, Cycle<Rule>> nodeToScc = new HashMap<Node<Rule>, Cycle<Rule>>(this.g.getNodes().size());
                for (Cycle<Rule> cycle : localSccs) {
                    for (Node<Rule> node : cycle) {
                        nodeToScc.put(node, cycle);
                    }
                }

                for (Edge<?, Rule> e : edges) {
                    Node<Rule> from = e.getStartNode();
                    Node<Rule> to = e.getEndNode();
                    Cycle<Rule> fromCycle = nodeToScc.get(from);
                    if (fromCycle != null && fromCycle == nodeToScc.get(to)) {
                        if (!this.calculateStarConnection(from.getObject(), to.getObject())) {
                            this.g.removeEdge(from, to);
                            changed = true;
                        }
                    }
                }
            }

            if (changed) {
                localSccs = this.computeSccs();
            }
        }

        return localSccs;
    }

    /**
     * returns the substitution when unifying cap_u(v) with s. Here s is taken
     * with 1. prefix var and u_to_v with 3. prefix var. Fresh vars from cap have 2. prefix.
     * Note that the connection between these nodes must be present in this graph.
     * (This implies that also Q-normal checks have been performed already!)
     * Otherwise the result may be anything including null.
     * @param s_to_t
     * @param u_to_v
     */
    public TRSSubstitution getConnectingSubstitution(Node<Rule> u_to_v, Node<Rule> s_to_t) {
        GeneralizedRule capped_u_to_v = this.capCalculator.getCappedDP(u_to_v.getObject());
        final TRSTerm cap_v = capped_u_to_v.getRight();
        final TRSFunctionApplication t = s_to_t.getObject().getLhsInStandardRepresentation();
        final TRSSubstitution result = cap_v.getMGU(t);

        if (Globals.DEBUG_FUHS) {
            if (result == null) {
                  System.err.println("NO connecting substitution found!");
                System.err.println("Rule Pair:  " + u_to_v.getObject() + " -> " + s_to_t.getObject());
            }
        }
        return result;
    }

    /**
     * returns the substitution when unifying cap_R^-1(u) with t. Here t is taken
     * with 1. prefix var and u_to_v with 3. prefix var. Fresh vars from cap have 2. prefix.
     * Note that the connection between these nodes must be present in this graph.
     * (This implies that also Q-normal checks have been performed already!)
     * Otherwise the result may be anything including null.
     * @param s_to_t
     * @param u_to_v
     */
    public TRSSubstitution getConnectingStarSubstitution(Node<Rule> s_to_t, Node<Rule> u_to_v) {

        final TRSTerm cap_u;

        if (this.QsuperR) {
            cap_u = this.capCalculator.getCapUsedRminusOneOfU(s_to_t.getObject(), u_to_v.getObject());
        } else {
            if (Globals.useAssertions) {
                assert(!this.capCalculator.getUnderlyingQTRS().isCollapsing());
            }
            cap_u = this.capCalculator.getCapRminusOneOfU(u_to_v.getObject());
        }

        final TRSTerm t = s_to_t.getObject().getRhsInStandardRepresentation();

        final TRSSubstitution result = t.getMGU(cap_u);

        if (Globals.DEBUG_FUHS) {
            if (result == null) {
                System.err.println("NO connecting star substitution found!");
                System.err.println("Rule Pair:  " + u_to_v.getObject() + " -> " + s_to_t.getObject());
            }
        }
        return result;
    }

    /**
     * returns the usable rules of a DP,
     * only available in innermost case
     * @param s_to_t
     */
    public Set<Rule> getUsableRules(Rule s_to_t) {
        return this.capCalculator.getUsableRules(s_to_t);
    }


    /**
     * checks whether this graph is one big SCC
     * @return
     */
    public boolean isSCC() {
        return this.sccs == null;
    }

    public boolean isGenuineSCC() {
        Set<Cycle<Rule>> sccs = this.g.getSCCs();
        return sccs.size() > 0;
    }

    /**
     * returns the set of subgraphs.
     * Must only be called if this graph is not a SCC!
     * (can be checked with isSCC)
     * @return
     */
    public Set<RelDepGraph> getSubSCCs() {
        Set<RelDepGraph> subSccs = new LinkedHashSet<RelDepGraph>(this.sccs.size());
        for (Set<Node<Rule>> scc : this.sccs) {
            subSccs.add(this.getSubGraph(scc));
        }
        return subSccs;
    }

    /**
     * returns the set of subgraphs. Must only be called if this graph is not a
     * SCC! (can be checked with isSCC)
     *
     * @return
     */
    public Set<RelDepGraph> getSubSCCs(boolean onlyReal) {
        Set<RelDepGraph> subSccs = new LinkedHashSet<RelDepGraph>(
                this.sccs.size());
        for (Set<Node<Rule>> scc : this.g.getSCCs(onlyReal)) {
            subSccs.add(this.getSubGraph(scc));
        }
        return subSccs;
    }

    /**
     * computes the set of nodes that are on a SCC of this graph. One must not
     * modifiy the returned set!
     */
    public Set<Node<Rule>> getNodesOnSCCs() {
        if (this.sccs == null) {
            return this.g.getNodes();
        } else {
            Set<Node<Rule>> nodes = new HashSet<Node<Rule>>(this.g.getNodes().size());
            for (Set<Node<Rule>> scc : this.sccs) {
                nodes.addAll(scc);
            }
            return nodes;
        }
    }

    public ImmutableSet<Rule> getP() {
        return ImmutableCreator.create(this.g.getNodeObjects());
    }

    public String toDOT() {
        return this.g.toDOT(false);
    }

    /**
     * returns the internal graph. This graph must not be modified,
     * but may only be used for lookup-reasons.
     */
    public Graph<Rule, ?> getGraph() {
        return this.g;
    }
}
