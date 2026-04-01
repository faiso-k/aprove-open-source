package aprove.verification.relative.RDTProblem;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * based on @see aprove.verification.dpframework.DPProblem.QDependencyGraph
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class RelDepGraph implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final Graph<CoupledPosDepTuple, ?> g;
    private final RelQUsableRules capCalculator; // the method to obtain capped terms (can be reused later!)
    private Set<CoupledPosDepTuple> marking;
    // this component contains the TRS R and Q!

    // TODO: deleted this, not sure what it's for
//    private final ProbQTransformationInfo transformationInfo; // values for heuristics of NRI-transformations.

    /* computed values */
    private final QTermSet Q;
    private final boolean QsuperR;
    private final Set<Cycle<CoupledPosDepTuple>> sccs; // the set of sccs of this graph, null if the graph itself is an SCC;
    // must be computed in the constructor
    private final Map<TRSFunctionApplication, Set<CoupledPosDepTuple>> usablePairsMap;

    private boolean atomic_graph = false;  // set to true if created by dep graph proc

    // ================================================================================
    // Constructors and Creators
    // ================================================================================
    
    /**
     * create Graph from scratch, if P is given, or start with "graph", if graph is given.
     * @param P - a set of DPs
     * @param graph a graph over DPs
     * @param sWithQ
     */
    private RelDepGraph(
        Set<CoupledPosDepTuple> d1,
        Set<CoupledPosDepTuple> d2,
        QTRSProblem sWithQ,
        Graph<CoupledPosDepTuple, ?> graph,
        Set<CoupledPosDepTuple> marking
    ) {
        if (Globals.useAssertions) {
            // EITHER graph&marking OR d1&d2 must be given
            assert ((d1 == null) == (d2 == null) == (graph != null) == (marking != null));
        }
        this.Q = sWithQ.getQ();
        this.capCalculator = sWithQ.getRelQUsableRulesCalculator();
        this.QsuperR = sWithQ.QsupersetOfLhsR();
        final Set<FunctionSymbol> defsOfR = sWithQ.getDefinedSymbolsOfR();
        if (graph == null) {
            int n = d1.size() + d2.size();
            Set<Node<CoupledPosDepTuple>> nodes = new LinkedHashSet<Node<CoupledPosDepTuple>>(n);
            this.marking = d2;  // TODO: check this is a hashset?
            for (CoupledPosDepTuple dp : d1) {
                nodes.add(new Node<CoupledPosDepTuple>(dp));
            }
            for (CoupledPosDepTuple dp : d2) {
                nodes.add(new Node<CoupledPosDepTuple>(dp));
            }
            this.g = new Graph<CoupledPosDepTuple, Object>(nodes);
//            this.transformationInfo = new ProbQTransformationInfo(nodes);

            // iterate through all possible edges
            Node<CoupledPosDepTuple>[] nodeArr = new Node[n];
            nodeArr = nodes.toArray(nodeArr);

            // first do crude approximation on root symbols
            // (this check requires non-collapsing rules!)
            // (only check nodes in sccs in more detail!)
            for (int i = 0; i < n; i++) {
                Node<CoupledPosDepTuple> fromDP = nodeArr[i];
                CoupledPosDepTuple fromDPRule = fromDP.getObject();
                for (int j = i + 1; j < n; j++) {
                    Node<CoupledPosDepTuple> toDP = nodeArr[j];
                    CoupledPosDepTuple toDPRule = toDP.getObject();
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
//            this.transformationInfo = new ProbQTransformationInfo(graph.getNodes());
            this.g = graph;
            this.marking = marking;
            Set<Pair<Node<CoupledPosDepTuple>, Node<CoupledPosDepTuple>>> delete = new LinkedHashSet<Pair<Node<CoupledPosDepTuple>, Node<CoupledPosDepTuple>>>();
            for (Edge<?, CoupledPosDepTuple> edge : this.g.getEdges()) {
                Node<CoupledPosDepTuple> start = edge.getStartNode();
                Node<CoupledPosDepTuple> end = edge.getEndNode();
                if (!this.calculateFastConnection(start.getObject(), end.getObject(), defsOfR)) {
                    delete.add(new Pair<Node<CoupledPosDepTuple>, Node<CoupledPosDepTuple>>(start, end));
                }
            }
            // now update graph
            for (Pair<Node<CoupledPosDepTuple>, Node<CoupledPosDepTuple>> edge : delete) {
                this.g.removeEdge(edge.x, edge.y);
            }
        }

        Pair<Set<Cycle<CoupledPosDepTuple>>, Map<TRSFunctionApplication, Set<CoupledPosDepTuple>>> sccsAndUsablePairsMap = this
                .checkEdgesOnSccs(this.computeSccs());
        this.sccs = sccsAndUsablePairsMap.x;
        this.usablePairsMap = sccsAndUsablePairsMap.y;
    }

    /**
     * create graph where P is a subset of the nodes in superGraph
     * => we do not have to check edges again
     * @param P
     * @param superGraph
     */
    private RelDepGraph(
        Set<Node<CoupledPosDepTuple>> P,
        RelDepGraph superGraph
    ) {
        if (Globals.useAssertions) {
            assert (superGraph.g.getNodes().containsAll(P));
        }
//        this.transformationInfo = superGraph.transformationInfo.getSubInfo(P);
        this.capCalculator = superGraph.capCalculator;
        this.g = superGraph.g.getSubGraph(P);
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;
        this.marking = superGraph.marking;

        //TODO: We do not need to compute this here again, as P is already fully evaluated
        Pair<Set<Cycle<CoupledPosDepTuple>>, Map<TRSFunctionApplication, Set<CoupledPosDepTuple>>> sccsAndUsablePairsMap = this
                .checkEdgesOnSccs(this.computeSccs());
        this.sccs = sccsAndUsablePairsMap.x;
        this.usablePairsMap = sccsAndUsablePairsMap.y;
    }

    /**
     * creates a DP-Graph from a given (fully evaluated graph) P and
     * the super DP-graph which contains the underlying TRS.
     * This constructor is intended for DP-transformations.
     * @param P
     * @param superGraph
     */
    private RelDepGraph(
        Graph<CoupledPosDepTuple, ?> g,
        RelDepGraph superGraph
    ) {
        this.capCalculator = superGraph.capCalculator;
        this.g = g;
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;
        this.marking = superGraph.marking;

        //TODO: We do not need to compute this here again, as P is already fully evaluated
        Pair<Set<Cycle<CoupledPosDepTuple>>, Map<TRSFunctionApplication, Set<CoupledPosDepTuple>>> sccsAndUsablePairsMap = this
                .checkEdgesOnSccs(this.computeSccs());
        this.sccs = sccsAndUsablePairsMap.x;
        this.usablePairsMap = sccsAndUsablePairsMap.y;
    }

    /**
     * create graph where P is a subset of the nodes in superGraph and
     * the edges are guaranteed to be included in the superGraph,
     * i.e. only existent edges may be deleted.
     * @param P
     * @param superGraph
     */
    private RelDepGraph(
        Set<Node<CoupledPosDepTuple>> P, 
        QTRSProblem sWithQ,
        RelDepGraph superGraph
    ) {
        if (Globals.useAssertions) {
            assert (superGraph.g.getNodes().containsAll(P));
        }
//        this.transformationInfo = superGraph.transformationInfo.getSubInfo(P);
        this.capCalculator = sWithQ.getRelQUsableRulesCalculator();
        this.Q = sWithQ.getQ();
        this.QsuperR = sWithQ.QsupersetOfLhsR();

        // create graph with corresponding node-set
        this.g = superGraph.g.getSubGraph(P);
        this.marking = new HashSet(superGraph.marking);
        this.marking.retainAll(P);  // TODO: remove nodes here

        Pair<Set<Cycle<CoupledPosDepTuple>>, Map<TRSFunctionApplication, Set<CoupledPosDepTuple>>> sccsAndUsablePairsMap = this
                .checkEdgesOnSccs(this.computeSccs());
        this.sccs = sccsAndUsablePairsMap.x;
        this.usablePairsMap = sccsAndUsablePairsMap.y;
    }

    private RelDepGraph(
        Set<CoupledPosDepTuple> g,
        QTRSProblem sWithQ,
        Graph<CoupledPosDepTuple, Object> dpGraph,
        RelDepGraph oldGraph
    ) {
        this.capCalculator = sWithQ.getRelQUsableRulesCalculator();
        this.g = dpGraph;
        this.Q = sWithQ.getQ();
        this.QsuperR = oldGraph.QsuperR;
        this.marking = oldGraph.marking;  // TODO: not sure about this

        Pair<Set<Cycle<CoupledPosDepTuple>>, Map<TRSFunctionApplication, Set<CoupledPosDepTuple>>> sccsAndUsablePairsMap = this
                .checkEdgesOnSccs(this.computeSccs());
        this.sccs = sccsAndUsablePairsMap.x;
        this.usablePairsMap = sccsAndUsablePairsMap.y;
    }

    /**
     * @param P
     * @param rWithQ
     * @return
     */
    public static RelDepGraph create(
        Set<CoupledPosDepTuple> d1,
        Set<CoupledPosDepTuple> d2,
        QTRSProblem sWithQ
) {
        return new RelDepGraph(d1, d2, sWithQ, null, null);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public ImmutableSet<CoupledPosDepTuple> getNodes() {
        return ImmutableCreator.create(this.g.getNodeObjects());
    }

    public ImmutableSet<CoupledPosDepTuple> getD1() {
        Set<CoupledPosDepTuple> res = new LinkedHashSet<CoupledPosDepTuple>();
        for (CoupledPosDepTuple node : this.getNodes()) {
            if (!marking.contains(node)) {
                res.add(node);
            }
        }
        return ImmutableCreator.create(res);
    }

    public ImmutableSet<CoupledPosDepTuple> getD2() {
        Set<CoupledPosDepTuple> res = new LinkedHashSet<CoupledPosDepTuple>();
        for (CoupledPosDepTuple node : this.getNodes()) {
            if (marking.contains(node)) {
                res.add(node);
            }
        }
        return ImmutableCreator.create(res);
    }

    /**
     * returns the internal graph. This graph must not be modified,
     * but may only be used for lookup-reasons.
     */
    public Graph<CoupledPosDepTuple, ?> getGraph() {
        return this.g;
    }

    public Map<TRSFunctionApplication, Set<CoupledPosDepTuple>> getUsablePairsMap() {
        return this.usablePairsMap;
    }

    public RelDepGraph getSubGraph(Set<Node<CoupledPosDepTuple>> P) {
        return new RelDepGraph(P, this);
    }

    public RelDepGraph getSubGraphFromPRules(Set<CoupledPosDepTuple> P) {
        Set<Node<CoupledPosDepTuple>> nodesForP = this.g.getNodesFromObjects(P);
        return new RelDepGraph(nodesForP, this);
    }

    public RelDepGraph getSubGraph2(Set<CoupledPosDepTuple> P) {  // TODO: clean up
        Set<Node<CoupledPosDepTuple>> nodesForP = this.g.getNodesFromObjects(P);
        return new RelDepGraph(nodesForP, this);
    }

    /**
     * creates a graph where P is a subset of the nodes and we draw edges
     * according to a new rWithQ
     */
    public RelDepGraph getSubGraph(Set<CoupledPosDepTuple> P, QTRSProblem sWithQ) {
        Set<Node<CoupledPosDepTuple>> nodesForP = this.g.getNodesFromObjects(P);
        return new RelDepGraph(nodesForP, sWithQ, this);
    }

    /**
     * checks whether this graph is one big SCC
     * @return
     */
    public boolean isSCC() {
        return this.sccs == null;
    }
    public boolean isAtomic() {
        return this.atomic_graph;
    }
    public boolean isMarked(CoupledPosDepTuple node) {
        return marking.contains(node);
    }
    public void unmarkAll() {
        this.marking = new HashSet<CoupledPosDepTuple>();
    }

    /**
     * checks whether there are any unusable Pairs
     * @return
     */
    public boolean doUnusablePairsExist() {
        for (Node<CoupledPosDepTuple> node : this.g.getNodes()) {
            CoupledPosDepTuple depTuple = node.getObject();
            for (TRSFunctionApplication t : depTuple.getAllTupleTermsInRHS()) {
                if (isUnusableTerm(t)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * checks whether the given Term is unusable
     * @return
     */
    public boolean isUnusableTerm(TRSFunctionApplication t) {
        TRSFunctionApplication tSTD = (TRSFunctionApplication) t.getStandardRenumbered();
        if (!usablePairsMap.containsKey(tSTD) || usablePairsMap.get(tSTD).isEmpty()) {
            return true;
        }
        return false;
    }

    public boolean isGenuineSCC() {
        Set<Cycle<CoupledPosDepTuple>> sccs = this.g.getSCCs();
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
        for (Set<Node<CoupledPosDepTuple>> scc : this.sccs) {
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
        for (Set<Node<CoupledPosDepTuple>> scc : this.g.getSCCs(onlyReal)) {
            subSccs.add(this.getSubGraph(scc));
        }
        return subSccs;
    }

    /**
     * computes the set of nodes that are on a SCC of this graph. One must not
     * modifiy the returned set!
     */
    public Set<Node<CoupledPosDepTuple>> getNodesOnSCCs() {
        if (this.sccs == null) {
            return this.g.getNodes();
        } else {
            Set<Node<CoupledPosDepTuple>> nodes = new HashSet<Node<CoupledPosDepTuple>>(
                    this.g.getNodes().size());
            for (Set<Node<CoupledPosDepTuple>> scc : this.sccs) {
                nodes.addAll(scc);
            }
            return nodes;
        }
    }

    // ================================================================================
    // Internals
    // ================================================================================

    /**
     * only checks on outermost symbols
     * @param from
     * @param to
     * @param defSymsOfR - the defined symbols of R.
     * @return false, if there is no edge
     */
    private boolean calculateFastConnection(
        CoupledPosDepTuple from,
        CoupledPosDepTuple to,
        Set<FunctionSymbol> defSymsOfR
    ) {
        Set<Pair<TRSFunctionApplication, Position>> posDepSet = from.getC();
        for (Pair<TRSFunctionApplication, Position> termPosPair : posDepSet) {
            TRSFunctionApplication term = termPosPair.x;
            final FunctionSymbol f = term.getRootSymbol();
            final FunctionSymbol g = to.getTupleRootSymbol();
            if (f.equals(g) || defSymsOfR.contains(f))
                return true;
        }
        return false;
    }

    public void setAtomic() {
        this.atomic_graph = true;
    }

    /**
     * does the usual forward checks with T/ICap.
     * Additionally, we compute the terms that can lead to the rule "to" (UsablePairs).
     * @param from
     * @param to
     * @return false, if the edge can be deleted
     */
    private Set<TRSFunctionApplication> calculateConnectionWithUsablePairs(CoupledPosDepTuple from,
                                                                           CoupledPosDepTuple to) {

        Set<TRSFunctionApplication> usablePairsSet = new HashSet<>();

        CappedCoupledPosDepTuple capped_s_to_t = this.capCalculator.getCappedDP(from);  // TODO: this is capped

        if (Globals.useAssertions) {
            for (TRSVariable v : capped_s_to_t.getVariables()) {
                assert (v.getName().startsWith(TRSTerm.SECOND_STANDARD_PREFIX)
                        || v.getName().startsWith(TRSTerm.THIRD_STANDARD_PREFIX));
            }
        }

        Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledRHS = capped_s_to_t
                .getRight();

            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> posDepSet = coupledRHS.getKey();

            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> termPosPair : posDepSet) {

            final TRSFunctionApplication u = to.getTupleLhsInStandardRepresentation();

            final TRSFunctionApplication cappedTerm = termPosPair.x.x;
            final TRSFunctionApplication normalTerm = termPosPair.x.y;

            final TRSSubstitution sigma = cappedTerm.getMGU(u);

            if (sigma == null) {
                continue;
            } else if (!this.Q.isEmpty()) {
                // no normal form conditions in Q = empty case

                // check normal form condition u sigma
                final TRSTerm u_sigma = u.applySubstitution(sigma);
                if (this.Q.canBeRewritten(u_sigma)) {
                    continue;
                } else {

                    TRSTerm s = capped_s_to_t.getTupleLeft();

                    // check normal form condition s sigma
                    final TRSTerm s_sigma = this.QsuperR ? s.applySubstitution(sigma) : s;
                    // s = s sigma in termination case
                    if (this.Q.canBeRewritten(s_sigma)) {
                        continue;
                    } else {
                        usablePairsSet.add(normalTerm);
                    }
                }
            } else {
                usablePairsSet.add(normalTerm);
            }
        }
        return usablePairsSet;
    }

    /**
     * does the usual forward checks with T/ICap
     * @param from
     * @param to
     * @return false, if the edge can be deleted
     */
    private boolean calculateConnection(CoupledPosDepTuple from, CoupledPosDepTuple to) {
        CappedCoupledPosDepTuple capped_s_to_t = this.capCalculator.getCappedDP(from);

        if (Globals.useAssertions) {
            for (TRSVariable v : capped_s_to_t.getVariables()) {
                assert (v.getName().startsWith(TRSTerm.SECOND_STANDARD_PREFIX)
                        || v.getName().startsWith(TRSTerm.THIRD_STANDARD_PREFIX));
            }
        }
        Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledRHS = capped_s_to_t.getRight();

        Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> posDepSet = coupledRHS.getKey();

        for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> termPosPair : posDepSet) {

            final TRSFunctionApplication u = to.getTupleLhsInStandardRepresentation();

            final TRSFunctionApplication cappedTerm = termPosPair.x.x;

            final TRSSubstitution sigma = cappedTerm.getMGU(u);

            if (sigma == null) {
                continue;
            } else if (!this.Q.isEmpty()) {
                // no normal form conditions in Q = empty case

                // check normal form condition u sigma
                final TRSTerm u_sigma = u.applySubstitution(sigma);
                if (this.Q.canBeRewritten(u_sigma)) {
                    continue;
                } else {

                    TRSTerm s = capped_s_to_t.getTupleLeft();

                    // check normal form condition s sigma
                    final TRSTerm s_sigma = this.QsuperR ? s.applySubstitution(sigma) : s;
                    // s = s sigma in termination case
                    if (this.Q.canBeRewritten(s_sigma)) {
                        continue;
                    } else {
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
     * does the star check. Either Q super R has to be true or the TRS must be non-collapsing.
     * Additionally, we compute the terms that can lead to the rule "to" (UsablePairs).
     * @param from
     * @param to
     * @return false, if edge can be deleted;
     */
    private Set<TRSFunctionApplication> calculateStarConnectionWithUsablePairs(
        CoupledPosDepTuple from,
        CoupledPosDepTuple to
    ) {
        Set<TRSFunctionApplication> usablePairsSet = new HashSet<>();

        final TRSTerm cap_u;

        if (this.QsuperR) {
            cap_u = this.capCalculator.getCapUsedRminusOneOfU(from, to);
        } else {
            if (Globals.useAssertions) {
                assert (!this.capCalculator.getUnderlyingQTRS().isCollapsing());
            }
            cap_u = this.capCalculator.getCapRminusOneOfU(to);
        }

        final Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledRHS = from.getRhsInStandardRepresentation();

        Set<Pair<TRSFunctionApplication, Position>> posDepSet = coupledRHS.getKey();

        for (Pair<TRSFunctionApplication, Position> termPosPair : posDepSet) {

            final TRSFunctionApplication term = termPosPair.x;

            final TRSSubstitution sigma = term.getMGU(cap_u);

            if (sigma == null) {
                continue;
            } else if (!cap_u.isVariable() && !this.Q.isEmpty()) {
                // do some Q-normal checks (if cap_u is variable, then we do not change anything, and s in Q-NF has been checked before

                final TRSTerm sSigma = from.getTupleLhsInStandardRepresentation().applySubstitution(sigma);
                if (this.Q.canBeRewritten(sSigma)) {
                    continue;
                } else {
                    usablePairsSet.add(term);
                }
            } else {
                usablePairsSet.add(term);
            }
        }

        return usablePairsSet;
    }

    /**
     * does the star check. Either Q super R has to be true or the TRS must be non-collapsing
     * @param from
     * @param to
     * @return false, if edge can be deleted;
     */
    private boolean calculateStarConnection(CoupledPosDepTuple from, CoupledPosDepTuple to) {
        if (Options.certifier.isRainbow()) {
            return true; // currently not supported by rainbow
        }

        final TRSTerm cap_u;

        if (this.QsuperR) {
            cap_u = this.capCalculator.getCapUsedRminusOneOfU(from, to);
        } else {
            if (Globals.useAssertions) {
                assert (!this.capCalculator.getUnderlyingQTRS().isCollapsing());
            }
            cap_u = this.capCalculator.getCapRminusOneOfU(to);
        }

        final Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledRHS = from.getRhsInStandardRepresentation();

        Set<Pair<TRSFunctionApplication, Position>> posDepSet = coupledRHS.getKey();

        for (Pair<TRSFunctionApplication, Position> termPosPair : posDepSet) {

            final TRSFunctionApplication term = termPosPair.x;

            final TRSSubstitution sigma = term.getMGU(cap_u);

            if (sigma == null) {
                continue;
            } else if (!cap_u.isVariable() && !this.Q.isEmpty()) {
                // do some Q-normal checks (if cap_u is variable, then we do not change anything, and s in Q-NF has been checked before

                final TRSTerm sSigma = from.getTupleLhsInStandardRepresentation().applySubstitution(sigma);
                if (this.Q.canBeRewritten(sSigma)) {
                    continue;
                } else {
                    return true;
                }
            } else {
                return true;
            }
        }
        return false;
    }

    private Set<Cycle<CoupledPosDepTuple>> computeSccs() {
        Set<Cycle<CoupledPosDepTuple>> sccs = this.g
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
     * Computes a finer connection on edges on sccs and compute the usablePairs
     */
    private Pair<Set<Cycle<CoupledPosDepTuple>>, Map<TRSFunctionApplication, Set<CoupledPosDepTuple>>> checkEdgesOnSccs(
            Set<Cycle<CoupledPosDepTuple>> localSccs) {
        Map<TRSFunctionApplication, Set<CoupledPosDepTuple>> usablePairsMap = new HashMap<>();
        List<Edge<?, CoupledPosDepTuple>> edges = new ArrayList<Edge<?, CoupledPosDepTuple>>(this.g.getEdges());
        boolean changed = false;
        if (localSccs == null) {
            for (Edge<?, CoupledPosDepTuple> e : edges) {
                Node<CoupledPosDepTuple> from = e.getStartNode();
                Node<CoupledPosDepTuple> to = e.getEndNode();
                Set<TRSFunctionApplication> connectionSet = this.calculateConnectionWithUsablePairs(from.getObject(),
                        to.getObject());
                if (connectionSet.isEmpty()) {
                    this.g.removeEdge(from, to);
                    changed = true;
                } else {
                    for (TRSFunctionApplication t : connectionSet) {
                        TRSFunctionApplication tSTD = (TRSFunctionApplication) t.getStandardRenumbered();
                        if (usablePairsMap.containsKey(tSTD)) {
                            Set<CoupledPosDepTuple> usableForSet = usablePairsMap.get(tSTD);
                            usableForSet.add(to.getObject());
                            usablePairsMap.put(tSTD, usableForSet);
                        } else {
                            Set<CoupledPosDepTuple> usableForSet = new HashSet<>();
                            usableForSet.add(to.getObject());
                            usablePairsMap.put(tSTD, usableForSet);
                        }
                    }
                }
            }
        } else {
            Map<Node<CoupledPosDepTuple>, Cycle<CoupledPosDepTuple>> nodeToScc = new HashMap<Node<CoupledPosDepTuple>, Cycle<CoupledPosDepTuple>>(
                    this.g.getNodes().size());
            for (Cycle<CoupledPosDepTuple> cycle : localSccs) {
                for (Node<CoupledPosDepTuple> node : cycle) {
                    nodeToScc.put(node, cycle);
                }
            }

            for (Edge<?, CoupledPosDepTuple> e : edges) {
                Node<CoupledPosDepTuple> from = e.getStartNode();
                Node<CoupledPosDepTuple> to = e.getEndNode();
                Cycle<CoupledPosDepTuple> fromCycle = nodeToScc.get(from);
                if (fromCycle != null && fromCycle == nodeToScc.get(to)) {
                    Set<TRSFunctionApplication> connectionSet = this
                            .calculateConnectionWithUsablePairs(from.getObject(), to.getObject());
                    if (connectionSet.isEmpty()) {
                        this.g.removeEdge(from, to);
                        changed = true;
                    } else {
                        for (TRSFunctionApplication t : connectionSet) {
                            TRSFunctionApplication tSTD = (TRSFunctionApplication) t.getStandardRenumbered();
                            if (usablePairsMap.containsKey(tSTD)) {
                                Set<CoupledPosDepTuple> usableForSet = usablePairsMap.get(tSTD);
                                usableForSet.add(to.getObject());
                                usablePairsMap.put(tSTD, usableForSet);
                            } else {
                                Set<CoupledPosDepTuple> usableForSet = new HashSet<>();
                                usableForSet.add(to.getObject());
                                usablePairsMap.put(tSTD, usableForSet);
                            }
                        }
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
            Map<TRSFunctionApplication, Set<CoupledPosDepTuple>> usablePairsMapStar = new HashMap<>();
            
            // in termination case there is no chance if we have collapsing rules to delete further edges
            edges = new ArrayList<Edge<?, CoupledPosDepTuple>>(this.g.getEdges());
            changed = false;
            if (localSccs == null) {
                for (Edge<?, CoupledPosDepTuple> e : edges) {
                    Node<CoupledPosDepTuple> from = e.getStartNode();
                    Node<CoupledPosDepTuple> to = e.getEndNode();
                    Set<TRSFunctionApplication> connectionSet = this.calculateStarConnectionWithUsablePairs(from.getObject(),
                            to.getObject());
                    if (connectionSet.isEmpty()) {
                        this.g.removeEdge(from, to);
                        changed = true;
                    } else {
                        for (TRSFunctionApplication t : connectionSet) {
                            TRSFunctionApplication tSTD = (TRSFunctionApplication) t.getStandardRenumbered();
                            if (usablePairsMapStar.containsKey(tSTD)) {
                                Set<CoupledPosDepTuple> usableForSet = usablePairsMapStar.get(tSTD);
                                usableForSet.add(to.getObject());
                                usablePairsMapStar.put(tSTD, usableForSet);
                            } else {
                                Set<CoupledPosDepTuple> usableForSet = new HashSet<>();
                                usableForSet.add(to.getObject());
                                usablePairsMapStar.put(tSTD, usableForSet);
                            }
                        }
                    }
                }
            } else {
                Map<Node<CoupledPosDepTuple>, Cycle<CoupledPosDepTuple>> nodeToScc = new HashMap<Node<CoupledPosDepTuple>, Cycle<CoupledPosDepTuple>>(
                        this.g.getNodes().size());
                for (Cycle<CoupledPosDepTuple> cycle : localSccs) {
                    for (Node<CoupledPosDepTuple> node : cycle) {
                        nodeToScc.put(node, cycle);
                    }
                }

                for (Edge<?, CoupledPosDepTuple> e : edges) {
                    Node<CoupledPosDepTuple> from = e.getStartNode();
                    Node<CoupledPosDepTuple> to = e.getEndNode();
                    Cycle<CoupledPosDepTuple> fromCycle = nodeToScc.get(from);
                    if (fromCycle != null && fromCycle == nodeToScc.get(to)) {
                        Set<TRSFunctionApplication> connectionSet = this.calculateStarConnectionWithUsablePairs(from.getObject(),
                                to.getObject());
                        if (connectionSet.isEmpty()) {
                            this.g.removeEdge(from, to);
                            changed = true;
                        } else {
                            for (TRSFunctionApplication t : connectionSet) {
                                TRSFunctionApplication tSTD = (TRSFunctionApplication) t.getStandardRenumbered();
                                if (usablePairsMapStar.containsKey(tSTD)) {
                                    Set<CoupledPosDepTuple> usableForSet = usablePairsMapStar.get(tSTD);
                                    usableForSet.add(to.getObject());
                                    usablePairsMapStar.put(tSTD, usableForSet);
                                } else {
                                    Set<CoupledPosDepTuple> usableForSet = new HashSet<>();
                                    usableForSet.add(to.getObject());
                                    usablePairsMapStar.put(tSTD, usableForSet);
                                }
                            }
                        }
                    }
                }
            }
            
            // Take the intersection of both usablePairsMaps
            Map<TRSFunctionApplication, Set<CoupledPosDepTuple>> usablePairsMapIntersection = new HashMap<>();
            for (Entry<TRSFunctionApplication, Set<CoupledPosDepTuple>> entry : usablePairsMap.entrySet()) {
                TRSFunctionApplication tSTD = entry.getKey();
                Set<CoupledPosDepTuple> set = entry.getValue();
                
                if (usablePairsMapStar.containsKey(tSTD)) {
                    Set<CoupledPosDepTuple> usableForSet = usablePairsMapStar.get(tSTD);
                    usableForSet.retainAll(set);
                    usablePairsMapIntersection.put(tSTD, usableForSet);
                }
            }

            if (changed) {
                localSccs = this.computeSccs();
            }
        }

        return new Pair<>(localSccs, usablePairsMap);
    }

    // ================================================================================
    // Utility
    // ================================================================================

    public String toDOT() {
        return this.g.toDOT(false);
    }

}
