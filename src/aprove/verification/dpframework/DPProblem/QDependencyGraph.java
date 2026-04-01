// TODO Spaghetticode. This must be reviewed!
package aprove.verification.dpframework.DPProblem;

import java.util.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Note that cap_R(...) and cap_{R^{-1}}(...) are stored during
 * computation of the DP graph. This is used by Narrowing,
 * Instantiation, ... processors (DP transformations). This is
 * the reason why these processors are applicable only if the
 * underlying problem has already been DP-graph-reduced.
 *
 * @author thiemann
 * @version $Id$
 */
public class QDependencyGraph implements Immutable {

    /*
     * real values
     */
    private final Graph<Rule, ?> g;
    private final QUsableRules capCalculator; // the method to obtain capped terms (can be reused later!)
      // this component contains the TRS R and Q!

    private final QTransformationInfo transformationInfo; // values for heuristics of NRI-transformations.

    /*
     * calculated values
     */
    private final QTermSet Q;
    private final boolean QsuperR;
    private final Set<Cycle<Rule>> sccs; // the set of sccs of this graph, null if the graph itself is an SCC;
                                   // must be computed in the constructor


    /**
     * create Graph from scratch, if P is given, or start with "graph", if graph is given.
     * @param P - a set of DPs
     * @param graph a graph over DPs
     * @param rWithQ
     */
    private QDependencyGraph(Set<Rule> P, QTRSProblem rWithQ, Graph<Rule,?> graph) {
        if (Globals.useAssertions) {
            assert ((P == null) == (graph != null)); // exactly one of graph and P must be given
        }
        this.Q = rWithQ.getQ();
        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.QsuperR = rWithQ.QsupersetOfLhsR();
        final Set<FunctionSymbol> defsOfR = rWithQ.getDefinedSymbolsOfR();
        if (graph == null) {
            int n = P.size();
            Set<Node<Rule>> nodes = new LinkedHashSet<Node<Rule>>(n);
            for (Rule dp : P) {
                nodes.add(new Node<Rule>(dp));
            }
            this.g = new Graph<Rule, Object>(nodes);
            this.transformationInfo = new QTransformationInfo(nodes);

            // iterate through all possible edges
            Node<Rule>[] nodeArr = new Node[n];
            nodeArr = nodes.toArray(nodeArr);

            // first do crude approximation on root symbols
            // (this check requires non-collapsing rules!)
            // (only check nodes in sccs in more detail!)
            for (int i = 0; i<n; i++) {
                Node<Rule> fromDP = nodeArr[i];
                Rule fromDPRule = fromDP.getObject();
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
        } else {
            // we have a given graph, but of course we have to check whether we can
            // delete additional edges
            this.transformationInfo = new QTransformationInfo(graph.getNodes());
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
    private QDependencyGraph(Set<Node<Rule>> P, QDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert(superGraph.g.getNodes().containsAll(P));
        }
        this.transformationInfo = superGraph.transformationInfo.getSubInfo(P);
        this.capCalculator = superGraph.capCalculator;
        this.g = superGraph.g.getSubGraph(P);
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;

        this.sccs = this.computeSccs();
    }

    /**
     * creates a DP-Graph from a given (fully evaluated graph) P and
     * the super DP-graph which contains the underlying TRS.
     * This constructor is intended for DP-transformations.
     * @param P
     * @param superGraph
     */
    private QDependencyGraph(Graph<Rule, ?> P, QTransformationInfo transformationInfo, QDependencyGraph superGraph) {
        this.transformationInfo = transformationInfo;
        this.capCalculator = superGraph.capCalculator;
        this.g = P;
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;

        this.sccs = this.computeSccs();
    }

    /**
     * creates a DP-Graph from a given DP-graph superGraph
     * and a collection of edges that should be dropped in the new graph.
     * @param P
     * @param superGraph
     */
    private QDependencyGraph(Collection<Pair<Node<Rule>, Node<Rule>>> dropTheseEdges, QDependencyGraph superGraph) {
        this.transformationInfo = superGraph.transformationInfo;
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

        this.sccs = this.computeSccs();
    }


    /**
     * create graph where P is a subset of the nodes in superGraph and
     * the edges are guaranteed to be included in the superGraph,
     * i.e. only existent edges may be deleted.
     * @param P
     * @param superGraph
     */
    private QDependencyGraph(Set<Node<Rule>> P, QTRSProblem rWithQ, QDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert(superGraph.g.getNodes().containsAll(P));
        }
        this.transformationInfo = superGraph.transformationInfo.getSubInfo(P);
        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.Q = rWithQ.getQ();
        this.QsuperR = rWithQ.QsupersetOfLhsR();

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
    private QDependencyGraph(QTRSProblem rWithQ, QDependencyGraph superGraph) {
        assert(superGraph.QsuperR);
        this.transformationInfo = superGraph.transformationInfo;
        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.Q = rWithQ.getQ();
        this.QsuperR = rWithQ.QsupersetOfLhsR();

        // create graph with corresponding node-set
        Graph<Rule, ?> supGraph = superGraph.g;
        this.g = supGraph.getSubGraph(supGraph.getNodes());

        this.sccs = null;
    }

    private QDependencyGraph(Set<Rule> P, QTRSProblem rWithQ, Graph<Rule, Object> dpGraph, QDependencyGraph oldGraph) {

        this.capCalculator = rWithQ.getQUsableRulesCalculator();
        this.g = dpGraph;
        this.Q = rWithQ.getQ();
        this.QsuperR = oldGraph.QsuperR;

        //TODO change this!
        this.transformationInfo = new QTransformationInfo(dpGraph.getNodes());

        this.sccs = this.checkEdgesOnSccs(oldGraph.sccs);

    }


    /**
     * creates a new DP-graph from this one by dropping a set of edges.
     * @param dropTheseEdges
     * @return
     */
    public QDependencyGraph getSubGraphByDroppingEdges(Collection<Pair<Node<Rule>, Node<Rule>>> dropTheseEdges) {
        return new QDependencyGraph(dropTheseEdges, this);
    }



    public QDependencyGraph getSubGraph(Set<Node<Rule>> P) {
        return new QDependencyGraph(P, this);
    }

    public QDependencyGraph getSubGraphFromPRules(Set<Rule> P) {
        Set<Node<Rule>> nodesForP = this.g.getNodesFromObjects(P);
        return new QDependencyGraph(nodesForP, this);
    }

    /**
     * creates a graph where P is a subset of the nodes and we draw edges
     * according to a new rWithQ
     */
    public QDependencyGraph getSubGraph(Set<Rule> P, QTRSProblem rWithQ) {
        Set<Node<Rule>> nodesForP = this.g.getNodesFromObjects(P);
        return new QDependencyGraph(nodesForP, rWithQ, this);
    }

    /**
     * returns the graph where we restrict R to the usableRules.
     * Here, this problem has to be innermost.
     * @param rWithQ
     * @return
     */
    public QDependencyGraph getUsableRulesSubGraph(QTRSProblem rWithQ) {
        return new QDependencyGraph(rWithQ, this);
    }



    /**
     * returns the graph when we replace s_to_t by the newDPs.
     * The transformation and position p is only needed to update
     * the transformation info for the heuristics.
     * Moreover, the new counter for the given transformation
     * of the newDPs is returned
     * @param transformation
     * @param s_to_t
     * @param newDPs
     * @param p
     * @return
     */
    public Pair<QDependencyGraph, Integer> getTransformedGraph(QDPTransformation transformation, Node<Rule> s_to_t, Set<Rule> newDPs, Position p) {
        Graph<Rule, ?> newGraph = this.g.getCopy();
        Node<Rule>[] newNodes = new Node[newDPs.size()];
        int i = 0;
        for (Rule newDP : newDPs) {
            Node<Rule> newNode = new Node<Rule>(newDP);
            newNodes[i] = newNode;
            newGraph.addNode(newNode);
            i++;
        }

        Set<FunctionSymbol> defsOfR = this.capCalculator.getUnderlyingQTRS().getDefinedSymbolsOfR();

        final boolean noStar = !this.QsuperR && this.capCalculator.getUnderlyingQTRS().isCollapsing();

        // incoming edges
        for (Node<Rule> prev : newGraph.getIn(s_to_t)) {
            if (!prev.equals(s_to_t)) {
                Rule prevRule = prev.getObject();
                for (Node<Rule> newDP : newNodes) {
                    Rule newDPRule = newDP.getObject();
                    if (this.calculateFastConnection(prevRule, newDPRule, defsOfR)) {
                        if (this.calculateConnection(prevRule, newDPRule)) {
                            if (noStar || this.calculateStarConnection(prevRule, newDPRule)) {
                                newGraph.addEdge(prev, newDP);
                            }
                        }
                    }
                }
            }
        }

        // outgoing edges
        for (Node<Rule> next : newGraph.getOut(s_to_t)) {
            if (!next.equals(s_to_t)) {
                Rule nextRule = next.getObject();
                for (Node<Rule> newDP : newNodes) {
                    Rule newDPRule = newDP.getObject();
                    if (this.calculateFastConnection(newDPRule, nextRule, defsOfR)) {
                        if (this.calculateConnection(newDPRule, nextRule)) {
                            if (noStar || this.calculateStarConnection(newDPRule, nextRule)) {
                                newGraph.addEdge(newDP, next);
                            }
                        }
                    }
                }
            }
        }

        // self loop
        if (newGraph.contains(s_to_t, s_to_t)) {
            for (Node<Rule> newDP : newNodes) {
                Rule newDPRule = newDP.getObject();
                for (Node<Rule> otherNew : newNodes) {
                    Rule otherNewRule = otherNew.getObject();
                    if (this.calculateFastConnection(newDPRule, otherNewRule, defsOfR)) {
                        if (this.calculateConnection(newDPRule, otherNewRule)) {
                            if (noStar || this.calculateStarConnection(newDPRule, otherNewRule)) {
                                newGraph.addEdge(newDP, otherNew);
                            }
                        }
                    }
                }
            }
        }

        // delete s_to_t
        newGraph.removeNode(s_to_t);

        // delete identical nodes (inserted rule with same connections already present)
        Set<Node<Rule>> reallyNewNodes = new HashSet<Node<Rule>>(newNodes.length);
        dp: for (Node<Rule> newDP : newNodes) {
            Set<Node<Rule>> possiblySame = newGraph.getAllNodesFromObject(newDP.getObject());
            if (possiblySame.size() > 1) {
                Set<Node<Rule>> out = newGraph.getOut(newDP);
                Set<Node<Rule>> in = newGraph.getIn(newDP);
                for (Node<Rule> oldNode : possiblySame) {
                    if (!oldNode.equals(newDP)) {
                        // if same incoming and outgoing connections, then we delete the newDP
                        if (newGraph.getOut(oldNode).equals(out) && newGraph.getIn(oldNode).equals(in)) {
                            newGraph.removeNode(newDP);
                            continue dp;
                        }
                    }
                }
                reallyNewNodes.add(newDP);
            } else {
                reallyNewNodes.add(newDP);
            }
        }

        Pair<QTransformationInfo, Integer> transInfoCounter = this.transformationInfo.getTransformedInfo(transformation, s_to_t, reallyNewNodes, p);

        return new Pair<QDependencyGraph, Integer>(
                new QDependencyGraph(newGraph, transInfoCounter.x, this),
                transInfoCounter.y);
    }


    /**
     * @param P note that the graph does not have to be the DP-graph but can be arbitary. However, the graph
     * will be modified when it is detected that one can delete some more edges!
     * @param rWithQ
     * @return
     */
    public static QDependencyGraph create(Graph<Rule, ?> P, QTRSProblem rWithQ) {
        return new QDependencyGraph(null, rWithQ, P);
    }


    /**
     * @param P
     * @param rWithQ
     * @return
     */
    public static QDependencyGraph create(Set<Rule> P, QTRSProblem rWithQ) {
        return new QDependencyGraph(P, rWithQ, null);
    }

    public static QDependencyGraph create(Set<Rule> P, QTRSProblem rWithQ, Graph<Rule, Object> dpGraph, QDependencyGraph oldGraph) {
        return new QDependencyGraph(P, rWithQ, dpGraph, oldGraph);
    }


    /**
     * only checks on outermost symbols
     * @param from
     * @param to
     * @param defSymsOfR - the defined symbols of R.
     * @return false, if there is no edge
     */
    private boolean calculateFastConnection(Rule from, Rule to, Set<FunctionSymbol> defSymsOfR) {
        TRSTerm t = from.getRight();
        if (t.isVariable()) {
            return true;
        } else {
            final FunctionSymbol f = ((TRSFunctionApplication) t).getRootSymbol();
            final FunctionSymbol g = to.getRootSymbol();
            return (f.equals(g) || defSymsOfR.contains(f));
        }
    }

    /**
     * does the usual forward checks with T/ICap
     * @param from
     * @param to
     * @return false, if the edge can be deleted
     */
    private boolean calculateConnection(Rule from, Rule to) {
        GeneralizedRule capped_s_to_t = this.capCalculator.getCappedDP(from);
        final TRSTerm cap_t = capped_s_to_t.getRight();
        if (Globals.useAssertions) {
            for (TRSVariable v : capped_s_to_t.getVariables()) {
                assert (v.getName().startsWith(TRSTerm.SECOND_STANDARD_PREFIX) || v.getName().startsWith(TRSTerm.THIRD_STANDARD_PREFIX));
            }
        }

        final TRSFunctionApplication u = to.getLhsInStandardRepresentation();

        final TRSSubstitution sigma = cap_t.getMGU(u);

        if (sigma == null) {
            return false;
        } else if (!this.Q.isEmpty()) {
            // no normal form conditions in Q = empty case

            // check normal form condition u sigma
            final TRSTerm u_sigma = u.applySubstitution(sigma);
            if (this.Q.canBeRewritten(u_sigma)) {
                return false;
            } else {

                TRSTerm s = capped_s_to_t.getLeft();

                // check normal form condition s sigma
                final TRSTerm s_sigma = this.QsuperR ? s.applySubstitution(sigma) : s;
                // s = s sigma in termination case
                if (this.Q.canBeRewritten(s_sigma)) {
                    return false;
                } else {
                    return true;
                }
            }
        } else {
            return true;
        }
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

        final TRSTerm cap_u;

        if (this.QsuperR) {
            cap_u = this.capCalculator.getCapUsedRminusOneOfU(from, to);
        } else {
            if (Globals.useAssertions) {
                assert(!this.capCalculator.getUnderlyingQTRS().isCollapsing());
            }
            cap_u = this.capCalculator.getCapRminusOneOfU(to);
        }

        final TRSTerm t = from.getRhsInStandardRepresentation();

        final TRSSubstitution sigma = t.getMGU(cap_u);

        if (sigma == null) {
            return false;
        } else if (!cap_u.isVariable() && !this.Q.isEmpty()) {
        // do some Q-normal checks (if cap_u is variable, then we do not change anything, and s in Q-NF has been checked before

            final TRSTerm sSigma = from.getLhsInStandardRepresentation().applySubstitution(sigma);
            if (this.Q.canBeRewritten(sSigma)) {
                return false;
            } else {
                return true;
            }
        } else {
            return true;
        }
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
     * returns the transformation Info. This info provides information
     * for the heuristics for the DP-Transformations Narrowing, R.,I.,FI.
     */
    public QTransformationInfo getTransformationInfo() {
        return this.transformationInfo;
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
    public Set<QDependencyGraph> getSubSCCs() {
        Set<QDependencyGraph> subSccs = new LinkedHashSet<QDependencyGraph>(this.sccs.size());
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
    public Set<QDependencyGraph> getSubSCCs(boolean onlyReal) {
        Set<QDependencyGraph> subSccs = new LinkedHashSet<QDependencyGraph>(
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
