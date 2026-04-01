package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Context-sensitive version of the Dependency Graph.
 *
 * @author Fabian Emmes
 * @version $Id$
 */
public class QCSDependencyGraph implements Immutable, Exportable {

    private final Graph<Rule, Object> graph;

    private final ImmutableLinkedHashSet<Cycle<Rule>> sccs;

    private final boolean allowStarEstimation = true;

    /**
     * Checks if (u, v) is _no_ chain, by checking if the pairs are rooted by
     * different head symbols.
     *
     * @param u
     *            first pair in tested chain.
     * @param v
     *            second pair of tested chain.
     * @return true if u and v can not be connected because of different head
     *         symbols.
     */
    private static boolean headSymbolUnconnectableCheck(final Rule u, final Rule v, final QCSDPProblem d) {
        if (u.getRight().isVariable()) {
            return false;
        }

        final FunctionSymbol h1 = ((TRSFunctionApplication) u.getRight()).getRootSymbol();

        final FunctionSymbol h2 = v.getRootSymbol();

        if (h1.equals(h2)) {
            return false;
        }

        final Set<FunctionSymbol> heads = d.getHeadSymbols();

        if (!heads.contains(h1) || !heads.contains(h2)) {
            return false;
        }

        return true;
    }

    private final ArrayList<Exportable> removalReasons = new ArrayList<Exportable>();

    /* TODO this should be setable in the strategy somehow */
    private final CapMuEstimation eCapMu = Globals.simpleCapMu ? new SimpleCapMu() : new ICapMu();

    public enum ECapMuEdgeRemovalReason {
        NoMGU, uNotNormal, sNotNormal
    };

    private class ECapMuUnconnectableReason implements Exportable {

        private final Rule s_to_t;

        private final Rule u_to_v;

        private final TRSTerm tCapped;

        private final ECapMuEdgeRemovalReason reason;

        ECapMuUnconnectableReason(final Rule s_to_t, final Rule u_to_v, final TRSTerm tCapped,
                final ECapMuEdgeRemovalReason reason) {
            this.reason = reason;
            this.s_to_t = s_to_t;
            this.u_to_v = u_to_v;
            this.tCapped = tCapped;
        }

        @Override
        public String export(final Export_Util o) {
            final StringBuilder s = new StringBuilder();
            s.append(o.export("The rules ") + o.export(this.s_to_t));
            s.append(o.export(" and ") + o.export(this.u_to_v));
            s.append(o.export(" form no chain, because ")
                + o.math("ECap" + o.sup(o.mu()) + "(" + o.export(this.s_to_t.getRight()) + ") = "
                    + o.export(this.tCapped)));
            switch (this.reason) {
            case NoMGU:
                s.append(o.export(" does not unify with " + o.export(this.u_to_v.getLeft()) + ". "));
                break;
            case uNotNormal:
                s.append(o.export(" unifies with " + o.export(this.u_to_v.getLeft()) + " using mgu " + o.sigma()
                    + ", but "));
                s.append(o.export(o.math(o.export(this.u_to_v.getLeft() + o.sigma()) + " is not in " + o.math("Q")
                    + "-" + o.mu() + "-normal form. ")));
                break;
            case sNotNormal:
                s.append(o.export(" unifies with " + o.export(this.u_to_v.getLeft()) + " using mgu " + o.sigma()
                    + ", but "));
                s.append(o.export(o.math(o.export(this.s_to_t.getLeft() + o.sigma()) + " is not in " + o.math("Q")
                    + "-" + o.mu() + "-normal form. ")));
                break;
            }
            return s.toString();
        }
    }

    public enum StarEstimationRemovalReason {
        NoMGU, uNotNormal, sNotNormal
    };

    private class StarEstimationUnconnectableReason implements Exportable {

        private final Rule s_to_t;

        private final Rule u_to_v;

        private final TRSTerm uCapped;

        private final StarEstimationRemovalReason reason;

        private final GeneralizedTRS rPrime;

        StarEstimationUnconnectableReason(final Rule s_to_t, final Rule u_to_v, final TRSTerm uCapped,
                final GeneralizedTRS rPrime, final StarEstimationRemovalReason reason) {
            this.rPrime = rPrime;
            this.reason = reason;
            this.s_to_t = s_to_t;
            this.u_to_v = u_to_v;
            this.uCapped = uCapped;
        }

        @Override
        public String export(final Export_Util o) {
            final StringBuilder s = new StringBuilder();
            s.append(o.export("The rules ") + o.export(this.s_to_t));
            s.append(o.export(" and ") + o.export(this.u_to_v));
            s.append(o.export(" form no chain, because ")
                + o.math("ECap" + o.sup(o.mu()) + o.sub(o.math("R'")) + "(" + o.export(this.u_to_v.getLeft()) + ") = "
                    + o.export(this.uCapped)));
            switch (this.reason) {
            case NoMGU:
                s.append(o.export(" does not unify with " + o.export(this.s_to_t.getRight()) + ". "));
                break;
            case uNotNormal:
                s.append(o.export(" unifies with " + o.export(this.u_to_v.getLeft()) + " using mgu " + o.sigma()
                    + ", but "));
                s.append(o.export(o.math(o.export(this.u_to_v.getLeft() + o.sigma()) + " is not in " + o.math("Q")
                    + "-" + o.mu() + "-normal form. ")));
                break;
            case sNotNormal:
                s.append(o.export(" unifies with " + o.export(this.u_to_v.getLeft()) + " using mgu " + o.sigma()
                    + ", but "));
                s.append(o.export(o.math(o.export(this.s_to_t.getLeft() + o.sigma()) + " is not in " + o.math("Q")
                    + "-" + o.mu() + "-normal form. ")));
                break;
            }
            s.append(o.cond_linebreak());
            s.append(o.export("R' = ") + o.set(this.rPrime.getRules(), Export_Util.RULES) + o.cond_linebreak());
            s.append(o.cond_linebreak());

            return s.toString();
        }
    }

    private static final Set<TRSTerm> emptyS = ImmutableCreator.create(new HashSet<TRSTerm>());

    private static final QTermSet emptyQ = new QTermSet(new ArrayList<TRSFunctionApplication>());

    private final boolean starEstimationUnconnectableCheck(final Rule s_to_t,
        final Rule u_to_v,
        final ReplacementMap mu,
        final QTermSet q,
        final QCSUsableRules ur) {

        final Rule s_to_t_Std = s_to_t.getWithRenumberedVariables(TRSTerm.STANDARD_PREFIX);
        final Rule u_to_v_Std = u_to_v.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);

        // build R'
        // no need to add u to s, since the mgu clears this up later
        final Set<Rule> usable = ur.estimatedCSUsableRules(s_to_t);

        // reverse usable rules
        final Set<TermPair> reversed = new LinkedHashSet<TermPair>();
        for (final Rule r : usable) {
            reversed.add(TermPair.create(r.getRight(), r.getLeft()));
        }

        final GeneralizedTRS rPrime = GeneralizedTRS.create(ImmutableCreator.create(reversed));

        // the resulting term uCapped is in third and second standard prefix
        // form
        final TRSTerm uCapped = this.eCapMu.capMu(mu, QCSDependencyGraph.emptyQ, rPrime, false, QCSDependencyGraph.emptyS, u_to_v_Std.getLeft());

        // s_to_t_Std is in first standard prefix
        final TRSSubstitution delta = uCapped.getMGU(s_to_t_Std.getRight());

        // not unifiable?
        if (delta == null) {
            this.removalReasons.add(new StarEstimationUnconnectableReason(s_to_t_Std, u_to_v_Std, uCapped, rPrime,
                StarEstimationRemovalReason.NoMGU));
            return true;
        }

        // s\delta not in Q-\mu-normal form?
        if (!mu.inQMuNormalForm(q, s_to_t_Std.getLeft().applySubstitution(delta))) {
            this.removalReasons.add(new StarEstimationUnconnectableReason(s_to_t_Std, u_to_v_Std, uCapped, rPrime,
                StarEstimationRemovalReason.sNotNormal));
            return true;
        }

        // u\delta not in Q-\mu-normal form?
        if (!mu.inQMuNormalForm(q, u_to_v_Std.getLeft().applySubstitution(delta))) {
            this.removalReasons.add(new StarEstimationUnconnectableReason(s_to_t_Std, u_to_v_Std, uCapped, rPrime,
                StarEstimationRemovalReason.uNotNormal));
            return true;
        }

        return false;
    }

    /**
     * based on [T07, Definition 3.9]
     *
     * @param s_to_t
     * @param u_to_v
     * @param mu
     * @param q
     * @param innermost
     * @param lhsR
     * @return
     */
    private final boolean eCapMuMuUnconnectableCheck(final Rule s_to_t,
        final Rule u_to_v,
        final ReplacementMap mu,
        final QTermSet q,
        final GeneralizedTRS r,
        final QCSDPProblem d) {

        final Rule s_to_t_Std = s_to_t.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        final Rule u_to_v_Std = u_to_v.getWithRenumberedVariables(TRSTerm.STANDARD_PREFIX);

        final TRSTerm tCapped = this.eCapMu.capMu(mu, q, r, d.isInnermost(), s_to_t_Std);
        // tCapped contains only vars in second and third standard prefix

        final TRSTerm s = s_to_t_Std.getLeft();
        final TRSTerm u = u_to_v_Std.getLeft();

        final TRSSubstitution sigma = tCapped.getMGU(u);

        if (sigma == null) {
            this.removalReasons.add(new ECapMuUnconnectableReason(s_to_t_Std, u_to_v_Std, tCapped,
                ECapMuEdgeRemovalReason.NoMGU));
            return true;
        }

        if (!mu.inQMuNormalForm(q, s.applySubstitution(sigma))) {
            this.removalReasons.add(new ECapMuUnconnectableReason(s_to_t_Std, u_to_v_Std, tCapped,
                ECapMuEdgeRemovalReason.sNotNormal));
            return true;
        }

        if (!mu.inQMuNormalForm(q, u.applySubstitution(sigma))) {
            this.removalReasons.add(new ECapMuUnconnectableReason(s_to_t_Std, u_to_v_Std, tCapped,
                ECapMuEdgeRemovalReason.uNotNormal));
            return true;
        }

        // could not prove that s->t, u->v form no chain
        return false;
    }

    /**
     * Uses different methods to determine if u and v cannot possibly form a
     * chain.
     *
     * @param u
     *            first pair
     * @param v
     *            second pair
     * @param mu
     *            the replacement map mu
     * @param q
     *            the set of terms Q
     * @param ur
     * @param lhsR
     *            the left hand sides of R, mapped by function symbol
     * @return true if u and v cannot possibly form a chain.
     */
    private final boolean unconnectableCheck(final Rule u,
        final Rule v,
        final ReplacementMap mu,
        final QTermSet q,
        final GeneralizedTRS r,
        final QCSUsableRules ur,
        final QCSDPProblem d) {
        if (QCSDependencyGraph.headSymbolUnconnectableCheck(u, v, d)) {
            return true;
        }

        if (this.eCapMuMuUnconnectableCheck(u, v, mu, q, r, d)) {
            return true;
        }

        if (this.allowStarEstimation) {
            if (this.starEstimationUnconnectableCheck(u, v, mu, q, ur)) {
                return true;
            }
        }

        // we cannot prove that (u, v) form no chain... yet
        return false;
    }

    /**
     * Generates dependency graph from scratch.
     *
     * @param info
     */
    private QCSDependencyGraph(final QCSDPProblem qcs) {
        this.graph = new Graph<Rule, Object>();

        final ReplacementMap mu = qcs.getReplacementMap();
        final QTermSet q = qcs.getQ();

        final GeneralizedTRS r = GeneralizedTRS.create(qcs.getRInPrefixForm(TRSTerm.STANDARD_PREFIX));

        final QCSUsableRules ur = qcs.getQCSUsableRules();

        final ArrayList<Node<Rule>> nodes = new ArrayList<Node<Rule>>();
        for (final Rule l_to_r : qcs.getDp()) {
            nodes.add(new Node<Rule>(l_to_r));
        }

        for (final Node<Rule> u : nodes) {
            for (final Node<Rule> v : nodes) {
                if (!this.unconnectableCheck(u.getObject(), v.getObject(), mu, q, r, ur, qcs)) {
                    this.graph.addEdge(u, v);
                }
            }
        }

        this.sccs = ImmutableCreator.create(this.graph.getSCCs());
    }

    public QCSDependencyGraph(final QCSDependencyGraph oldDPGraph, final Cycle<Rule> scc) {
        this.graph = oldDPGraph.graph.getSubGraph(scc);
        this.sccs = ImmutableCreator.create(this.graph.getSCCs());
    }

    public QCSDependencyGraph(final QCSDependencyGraph oldGraph, final QCSDPProblem qcs) {
        this.graph = new Graph<Rule, Object>();

        final ReplacementMap mu = qcs.getReplacementMap();
        final QTermSet q = qcs.getQ();

        final GeneralizedTRS r = GeneralizedTRS.create(qcs.getRInPrefixForm(TRSTerm.STANDARD_PREFIX));

        final QCSUsableRules ur = qcs.getQCSUsableRules();

        final ImmutableSet<Rule> pairs = qcs.getDp();

        for (final Node<Rule> node : oldGraph.getNodes()) {
            if (pairs.contains(node.getObject())) {
                this.graph.addNode(node);
            }
        }

        for (final Edge<Object, Rule> edge : oldGraph.getGraph().getEdges()) {
            final Node<Rule> u = edge.getStartNode();
            final Node<Rule> v = edge.getEndNode();

            if (!pairs.contains(u.getObject())) {
                continue;
            }

            if (!pairs.contains(v.getObject())) {
                continue;
            }

            if (!this.unconnectableCheck(u.getObject(), v.getObject(), mu, q, r, ur, qcs)) {
                this.graph.addEdge(u, v);
            }
        }

        this.sccs = ImmutableCreator.create(this.graph.getSCCs());
    }

    /**
     * Generates a new Dependency Graph for a problem, based on the oldGraph,
     * where oldPair will be substituted by newPairs. Should be only needed for
     * processors doing pair transformations.
     *
     * @param oldGraph
     * @param problem
     * @param oldPair
     * @param newPairs
     * @return
     */
    private QCSDependencyGraph(final QCSDependencyGraph oldGraph, final QCSDPProblem problem, final Rule oldPair,
            final ImmutableSet<Rule> newPairs, final boolean reconnectRhs) {
        this.graph = oldGraph.graph.getCopy();

        final Node<Rule> oldNode = this.graph.getNodeFromObject(oldPair);
        final Set<Node<Rule>> outNodes = this.graph.getOut(oldNode);
        final Set<Node<Rule>> inNodes = this.graph.getIn(oldNode);

        boolean selfConnected = false;
        if (outNodes.contains(oldNode) || inNodes.contains(oldNode)) {
            selfConnected = true;
        }

        this.graph.removeNode(oldNode);

        // remove self references of node
        outNodes.remove(oldNode);
        inNodes.remove(oldNode);

        final ReplacementMap mu = problem.getReplacementMap();
        final QTermSet q = problem.getQ();

        final GeneralizedTRS r = GeneralizedTRS.create(problem.getRInPrefixForm(TRSTerm.STANDARD_PREFIX));

        final QCSUsableRules ur = problem.getQCSUsableRules();

        final Set<Node<Rule>> newNodes = new LinkedHashSet<Node<Rule>>();
        for (final Rule newPair : newPairs) {
            newNodes.add(new Node<Rule>(newPair));
        }

        for (final Node<Rule> newNode : newNodes) {
            final Rule newPair = newNode.getObject();

            // check incoming edges
            for (final Node<Rule> uNode : inNodes) {
                final Rule u = uNode.getObject();

                if (!this.unconnectableCheck(u, newPair, mu, q, r, ur, problem)) {
                    this.graph.addEdge(uNode, newNode);
                }
            }

            if (reconnectRhs) {
                // must reconnect rhs to all possible nodes
                // check all old pairs
                for (final Node<Rule> uNode : oldGraph.graph.getNodes()) {
                    // must NOT connect to old replaced pair
                    if (uNode.getObject().equals(oldPair)) {
                        continue;
                    }

                    if (!this.unconnectableCheck(newPair, uNode.getObject(), mu, q, r, ur, problem)) {
                        this.graph.addEdge(newNode, uNode);
                    }
                }
                // check all new pairs
                for (final Node<Rule> uNode : newNodes) {
                    if (!this.unconnectableCheck(newPair, uNode.getObject(), mu, q, r, ur, problem)) {
                        this.graph.addEdge(newNode, uNode);
                    }
                }
            } else {
                // check outgoing edges
                for (final Node<Rule> uNode : outNodes) {
                    final Rule u = uNode.getObject();

                    if (!this.unconnectableCheck(newPair, u, mu, q, r, ur, problem)) {
                        this.graph.addEdge(newNode, uNode);
                    }
                }
            }
        }

        // check connections between the new pairs, if the old one was self looping
        if (selfConnected || reconnectRhs) {
            for (final Node<Rule> s_to_t : newNodes) {
                for (final Node<Rule> u_to_v : newNodes) {
                    if (!this.unconnectableCheck(s_to_t.getObject(), u_to_v.getObject(), mu, q, r, ur, problem)) {
                        this.graph.addEdge(s_to_t, u_to_v);
                    }

                }
            }
        }

        this.sccs = ImmutableCreator.create(this.graph.getSCCs());
    }

    public static QCSDependencyGraph create(final QCSDPProblem qcs) {
        return new QCSDependencyGraph(qcs);
    }

    /**
     * Create a new {@link QCSDependencyGraph} for a (changed)
     * {@link QCSDPProblem} under the hypothesis, that no new edges are
     * possible.
     *
     * @param oldGraph
     * @param qcs
     * @return
     */
    public static QCSDependencyGraph create(final QCSDependencyGraph oldGraph, final QCSDPProblem qcs) {
        return new QCSDependencyGraph(oldGraph, qcs);
    }

    public final Graph<Rule, Object> getGraph() {
        return this.graph;
    }

    public final ImmutableLinkedHashSet<Cycle<Rule>> getSccs() {
        return this.sccs;
    }

    /**
     * @return true, if the graph is separable to several SCCS
     */
    public final boolean isSeperable() {
        return this.sccs.size() > 1;
    }

    public Set<QCSDependencyGraph> getSccSubGraphs() {
        final Set<QCSDependencyGraph> subGraphs = new LinkedHashSet<QCSDependencyGraph>();
        for (final Cycle<Rule> scc : this.sccs) {
            subGraphs.add(new QCSDependencyGraph(this, scc));
        }
        return subGraphs;
    }

    public ImmutableSet<Node<Rule>> getNodes() {
        return ImmutableCreator.create(this.graph.getNodes());
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        for (final Exportable reason : this.removalReasons) {
            s.append(reason.export(o));
        }
        return s.toString();
    }

    /**
     * Generates a new Dependency Graph for a problem, based on the oldGraph,
     * where oldPair will be substituted by newPairs.
     *
     * @param oldGraph
     * @param problem
     * @param oldPair
     * @param newPairs
     * @return
     */
    public static QCSDependencyGraph create(final QCSDependencyGraph oldGraph,
        final QCSDPProblem problem,
        final Rule oldPair,
        final ImmutableSet<Rule> newPairs,
        final boolean reconnectRhs) {
        return new QCSDependencyGraph(oldGraph, problem, oldPair, newPairs, reconnectRhs);
    }
}
