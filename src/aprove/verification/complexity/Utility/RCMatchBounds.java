package aprove.verification.complexity.Utility;

import java.util.*;
import java.util.Map.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxTrsProblem.Processors.CpxTrsMatchBoundsProcessor.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

final class AnnotatedFS {
    final FunctionSymbol functionSymbol;
    final int height;
    final int iteration; // iteration in which this symbol was added to an edge label

    AnnotatedFS(final int h, final FunctionSymbol f, final int iteration) {
        this.height = h;
        this.functionSymbol = f;
        this.iteration = iteration;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final AnnotatedFS other = (AnnotatedFS) obj;
        if (this.functionSymbol == null) {
            if (other.functionSymbol != null) {
                return false;
            }
        } else if (!this.functionSymbol.equals(other.functionSymbol)) {
            return false;
        }
        if (this.height != other.height) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.functionSymbol == null) ? 0 : this.functionSymbol.hashCode());
        result = prime * result + this.height;
        return result;
    }

    @Override
    public String toString() {
        return this.functionSymbol + "|" + this.height;
    }
}

final class PathRequest {
    final Node<Object> from;

    final int height;

    final ImmutableArrayList<FunctionSymbol> p;
    final Node<Object> to;

    PathRequest(final Node<Object> from, final int height, final ImmutableArrayList<FunctionSymbol> p, final Node<Object> to) {
        this.from = from;
        this.height = height;
        this.p = p;
        this.to = to;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final PathRequest other = (PathRequest) obj;
        if (this.from == null) {
            if (other.from != null) {
                return false;
            }
        } else if (!this.from.equals(other.from)) {
            return false;
        }
        if (this.height != other.height) {
            return false;
        }
        if (this.p == null) {
            if (other.p != null) {
                return false;
            }
        } else if (!this.p.equals(other.p)) {
            return false;
        }
        if (this.to == null) {
            if (other.to != null) {
                return false;
            }
        } else if (!this.to.equals(other.to)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.from == null) ? 0 : this.from.hashCode());
        result = prime * result + this.height;
        result = prime * result + ((this.p == null) ? 0 : this.p.hashCode());
        result = prime * result + ((this.to == null) ? 0 : this.to.hashCode());
        return result;
    }

    @Override
    public String toString() {
        return "[from=" + this.from + ", height=" + this.height + ", p=" + this.p + ", to=" + this.to + "]";
    }
}

/**
 * MatchBounds for RuntimeComplexity on SRSs. Separate from class MatchBound.
 */
public class RCMatchBounds {
    public class CertificateGraph extends SimpleGraph<Object, Set<AnnotatedFS>> implements DOT_Able, Exportable {

        public final boolean backwardScan;

        private final ImmutableSet<Node<Object>> endNodes;

        public final boolean forwardScan;

        private int iteration = 0;

        private int numNodes = 0;

        public final boolean reversed;

        private final boolean splitEnds;

        private final Node<Object> startNode;

        private final int maxMatchBound;

        private final int maxNodes;

        private final int maxIterations;

        private CertificateGraph() throws LimitExceededException {
            this.forwardScan = RCMatchBounds.this.arguments.forwardScan;
            this.backwardScan = RCMatchBounds.this.arguments.backwardScan;
            this.reversed = RCMatchBounds.this.arguments.reversed;
            this.splitEnds = RCMatchBounds.this.arguments.splitEnds;
            this.maxMatchBound = RCMatchBounds.this.arguments.maxMatchBound;
            this.maxNodes = RCMatchBounds.this.arguments.maxNodes;
            this.maxIterations = RCMatchBounds.this.arguments.maxIterations;

            this.startNode = this.newNode();
            final Set<Node<Object>> endNodes = new LinkedHashSet<Node<Object>>();

            if (this.splitEnds) {
                for (final FunctionSymbol f : RCMatchBounds.this.defined) {
                    final Node<Object> en = this.newNode();
                    endNodes.add(en);
                    this.checkEdge(this.startNode, en, 0, f);
                }
            } else {
                final Node<Object> en = this.newNode();
                endNodes.add(en);
                for (final FunctionSymbol f : RCMatchBounds.this.defined) {
                    this.checkEdge(this.startNode, en, 0, f);
                }
            }

            this.endNodes = ImmutableCreator.create(endNodes);

            if (this.reversed) {
                for (final FunctionSymbol f : RCMatchBounds.this.signature) {
                    if (RCMatchBounds.this.defined.contains(f)) {
                        continue;
                    }
                    this.checkEdge(this.startNode, this.startNode, 0, f);
                }
            } else {
                for (final Node<Object> endNode : endNodes) {
                    for (final FunctionSymbol f : RCMatchBounds.this.signature) {
                        if (RCMatchBounds.this.defined.contains(f)) {
                            continue;
                        }
                        this.checkEdge(endNode, endNode, 0, f);
                    }
                }
            }
        }

        private void addPath(final PathRequest r) throws LimitExceededException {
            final int h = r.height;
            final ImmutableArrayList<FunctionSymbol> p = r.p;
            final int l = p.size();

            Node<Object> start = r.from;
            int startPos = 0;

            Node<Object> end = r.to;
            int endPos = l - 1;
            // make sure there is a path of height h from start over p to end

            LinkedHashSet<Node<Object>> startSet = new LinkedHashSet<Node<Object>>();
            startSet.add(start);
            while (startPos < l - 1) {
                final FunctionSymbol f = p.get(startPos);
                final LinkedHashSet<Node<Object>> newStartSet = new LinkedHashSet<Node<Object>>();
                for (final Node<Object> n : startSet) {
                    final Set<Edge<Set<AnnotatedFS>, Object>> oe = this.getOutEdges(n);
                    for (final Edge<Set<AnnotatedFS>, Object> e : oe) {
                        for (final AnnotatedFS label : e.getObject()) {
                            if (label.height == h && label.functionSymbol == f) {
                                newStartSet.add(e.getEndNode());
                            }
                        }
                    }
                }
                if (newStartSet.isEmpty()) {
                    break;
                }
                startSet = newStartSet;
                startPos++;
            }

            if (startPos == l) {
                return;
            }

            if (this.forwardScan) {
                start = startSet.iterator().next();
            } else {
                startPos = 0;
            }

            assert startPos <= endPos;

            if (this.backwardScan) {
                LinkedHashSet<Node<Object>> endSet = new LinkedHashSet<Node<Object>>();
                endSet.add(end);

                while (startPos < endPos) {
                    final FunctionSymbol f = p.get(endPos);
                    final LinkedHashSet<Node<Object>> newEndSet = new LinkedHashSet<Node<Object>>();

                    for (final Node<Object> n : endSet) {
                        final Set<Edge<Set<AnnotatedFS>, Object>> ie = this.getInEdges(n);
                        for (final Edge<Set<AnnotatedFS>, Object> e : ie) {
                            for (final AnnotatedFS label : e.getObject()) {
                                if (label.height == h && label.functionSymbol == f) {
                                    newEndSet.add(e.getStartNode());
                                    break;
                                }
                            }
                        }
                    }
                    if (newEndSet.isEmpty()) {
                        break;
                    }

                    endSet = newEndSet;
                    endPos--;
                }

                assert startPos <= endPos;
                end = endSet.iterator().next();
            }

            Node<Object> currentNode = start;
            for (int currentPos = startPos; currentPos < endPos; currentPos++) {
                final Node<Object> newNode = this.newNode();
                this.checkEdge(currentNode, newNode, h, p.get(currentPos));
                currentNode = newNode;
            }
            this.checkEdge(currentNode, end, h, p.get(endPos));
        }

        private void checkEdge(final Node<Object> start, final Node<Object> end, final Integer i, final FunctionSymbol f)
                throws LimitExceededException {
            if (i > this.maxMatchBound) {
                throw new LimitExceededException("Maximal MatchBound limit exceeded.");
            }

            Edge<Set<AnnotatedFS>, Object> edge = this.getEdge(start, end);
            if (edge == null) {
                edge = new Edge<Set<AnnotatedFS>, Object>(start, end, new LinkedHashSet<AnnotatedFS>());
                this.addEdge(edge);
            }
            final Set<AnnotatedFS> syms = edge.getObject();
            final AnnotatedFS p = new AnnotatedFS(i, f, this.iteration);
            syms.add(p);
        }

        private void checkNode(final Node<Object> currentNode,
            final Node<Object> startNode,
            final LinkedHashSet<PathRequest> requests,
            final Integer minHeight,
            final Matcher matcher,
            final boolean sawLastIteration) {

            if (sawLastIteration) {
                for (final ImmutableArrayList<FunctionSymbol> lhs : matcher.lhss) {
                    assert minHeight != null; // because the root matcher has no LHSs
                    requests.add(new PathRequest(startNode, minHeight + 1, lhs, currentNode));
                }
            }

            final Set<Edge<Set<AnnotatedFS>, Object>> outEdges = this.getOutEdges(currentNode);

            for (final Edge<Set<AnnotatedFS>, Object> e : outEdges) {
                final Node<Object> dest = e.getEndNode();
                final Set<AnnotatedFS> label = e.getObject();
                for (final Entry<FunctionSymbol, Matcher> c : matcher.children.entrySet()) {
                    final FunctionSymbol f = c.getKey();
                    for (final AnnotatedFS l : label) {
                        if (!l.functionSymbol.equals(f)) {
                            continue;
                        }
                        final int newMinHeight = minHeight != null && minHeight < l.height ? minHeight : l.height;
                        final boolean localSLI = sawLastIteration || (l.iteration == this.iteration - 1);
                        this.checkNode(dest, startNode, requests, newMinHeight, c.getValue(), localSLI);
                    }
                }
            }
        }

        private boolean doIteration() throws LimitExceededException {
            this.iteration++;

            if (this.iteration > this.maxIterations) {
                throw new LimitExceededException("Maximal number of iterations exceeded.");
            }

            final LinkedHashSet<PathRequest> requestedPaths = new LinkedHashSet<PathRequest>();

            for (final Node<Object> n : this.getNodes()) {
                this.checkNode(n, n, requestedPaths, null, RCMatchBounds.this.matcher, false);
            }

            for (final PathRequest req : requestedPaths) {
                this.addPath(req);
            }

            return !requestedPaths.isEmpty();
        }

        public ImmutableSet<Node<Object>> getEndNodes() {
            return this.endNodes;
        }

        public int getIteration() {
            return this.iteration;
        }

        public int getMatchBound() {
            int h = 0;
            for (final Edge<Set<AnnotatedFS>, Object> multiEdge : this.getEdges()) {
                final Set<AnnotatedFS> edges = multiEdge.getObject();
                for (final AnnotatedFS e : edges) {
                    h = Math.max(h, e.height);
                }
            }
            return h;
        }

        public int getNumNodes() {
            return this.numNodes;
        }

        public Node<Object> getStartNode() {
            return this.startNode;
        }

        public boolean isBackwardScan() {
            return this.backwardScan;
        }

        public boolean isForwardScan() {
            return this.forwardScan;
        }

        public boolean isReversed() {
            return this.reversed;
        }

        public boolean isSplitEnds() {
            return this.splitEnds;
        }

        /*
        @Override
        public String toString() {
            return super.toSaveDOTwithEdges();
        }
        */

        private Node<Object> newNode() throws LimitExceededException {
            this.numNodes++;
            if (this.numNodes > this.maxNodes) {
                throw new LimitExceededException("Maximal number of nodes exceeded.");
            }
            return new Node<Object>();
        }

        @Override
        public String export(final Export_Util o) {
            final StringBuffer sb = new StringBuffer();

            sb.append("Start state: " + this.startNode + o.newline());
            sb.append("Accept states: " + this.endNodes + o.newline());
            sb.append("Transitions:" + o.newline());

            for (final Edge<Set<AnnotatedFS>, Object> edge : this.getEdges()) {
                sb.append(edge.getStartNode());
                sb.append(o.rightarrow());
                sb.append(edge.getEndNode());
                sb.append(edge.getObject());
                sb.append(o.newline());
            }
            return sb.toString();
        }

        public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
            final Element boundProofTag = CPFTag.BOUNDS.createElement(doc);

            boundProofTag.appendChild(CPFTag.TYPE.create(doc, CPFTag.MATCH.create(doc)));
            boundProofTag.appendChild(CPFTag.BOUND.create(doc,this.getMatchBound()));

            final Element finalStatesTag = CPFTag.FINAL_STATES.create(doc);
            for (final Node<Object> state : this.endNodes) {
                finalStatesTag.appendChild(CPFTag.STATE.create(doc, state.getNodeNumber()));
            }
            boundProofTag.appendChild(finalStatesTag);
            final Element treeAutomatonTag = CPFTag.TREE_AUTOMATON.create(doc);
            final Element finalStatesTagCopy = CPFTag.FINAL_STATES.create(doc);
            final Set<Integer> allFinalNodes = new HashSet<>();
            for (final Node<Object> state : this.endNodes) {
                allFinalNodes.add(state.getNodeNumber());
            }
            allFinalNodes.add(this.startNode.getNodeNumber());
            for (final int state : allFinalNodes) {
                finalStatesTagCopy.appendChild(CPFTag.STATE.create(doc, state));
            }
            treeAutomatonTag.appendChild(finalStatesTagCopy);

            final Element transitions = CPFTag.TRANSITIONS.create(doc);
            for (final Edge<Set<AnnotatedFS>, Object> edge : this.getEdges()) {
                final int start = edge.getStartNode().getNodeNumber();
                final int end = edge.getEndNode().getNodeNumber();
                for (final AnnotatedFS fs : edge.getObject()) {
                    final FunctionSymbol f = fs.functionSymbol;
                    final int height = fs.height;
                    final Element transitionTag = CPFTag.TRANSITION.create(doc);
                    // as tree automaton, we require an edge from f(end) -> start.
                    final Element lhs = CPFTag.LHS.create(
                        doc,
                        f.toCPF(doc, xmlMetaData),
                        CPFTag.HEIGHT.create(doc, height));
                    if (f.getArity() == 1) {
                        lhs.appendChild(CPFTag.STATE.create(doc, end));
                    } else {
                        assert (f.getArity() == 0);
                        // this is the dangerous case: here we have a constant, but the
                        // MB routine treated it like a unary symbol. Hopefully, dropping
                        // the argument state does not matter at this point.
                        // however, so far all generated proofs in this way are so far
                        // accepted by CeTA, so let's leave it in
                        // (the alternative would be to demand exactly unary for CPF,
                        //  or to have constant-to-unary as separate processor)
                    }
                    transitionTag.appendChild(lhs);
                    transitionTag.appendChild(CPFTag.RHS.create(doc, CPFTag.STATE.create(doc, start)));
                    transitions.appendChild(transitionTag);
                }
            }
            treeAutomatonTag.appendChild(transitions);
            boundProofTag.appendChild(treeAutomatonTag);
            return boundProofTag;
        }

    }

    class Matcher {
        Map<FunctionSymbol, Matcher> children = new LinkedHashMap<FunctionSymbol, RCMatchBounds.Matcher>();
        Set<ImmutableArrayList<FunctionSymbol>> lhss = new LinkedHashSet<ImmutableArrayList<FunctionSymbol>>();

        void addRhs(final ImmutableArrayList<FunctionSymbol> rhs, final Set<FunctionSymbol> signature) {
            if (rhs.size() > 0) {
                this.lhss.add(rhs);
                return;
            }

            // if the RHS was only a variable...
            for (final FunctionSymbol f : signature) {
                final Matcher child = this.getOrCreateChild(f);
                final ArrayList<FunctionSymbol> alf = new ArrayList<FunctionSymbol>();
                alf.add(f);
                child.addRhs(ImmutableCreator.create(alf), signature);
            }
        }

        Matcher createPath(final Iterator<FunctionSymbol> i) {
            if (!i.hasNext()) {
                return this;
            }
            final FunctionSymbol f = i.next();
            return this.getOrCreateChild(f).createPath(i);
        }

        Matcher getOrCreateChild(final FunctionSymbol f) {
            Matcher child = this.children.get(f);
            if (child == null) {
                child = new Matcher();
                this.children.put(f, child);
            }
            return child;
        }
    }

    private final Arguments arguments;
    private final ImmutableSet<FunctionSymbol> defined;
    private final Matcher matcher;
    private final ImmutableSet<FunctionSymbol> signature;

    public RCMatchBounds(final Iterable<Rule> rules, final Arguments arguments) {

        final Set<FunctionSymbol> defined = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();
        for (final Rule r : rules) {
            signature.addAll(r.getFunctionSymbols());
            defined.add(r.getRootSymbol());
        }

        this.signature = ImmutableCreator.create(signature);
        this.defined = ImmutableCreator.create(defined);
        this.matcher = new Matcher();
        this.arguments = arguments;

        for (final Rule r : rules) {
            ImmutableArrayList<FunctionSymbol> lhs = this.scanTerm(r.getLeft());
            ImmutableArrayList<FunctionSymbol> rhs = this.scanTerm(r.getRight());

            if (this.arguments.reversed) {
                final ArrayList<FunctionSymbol> lhsRev = new ArrayList<FunctionSymbol>();
                lhsRev.addAll(lhs);
                Collections.reverse(lhsRev);
                lhs = ImmutableCreator.create(lhsRev);

                final ArrayList<FunctionSymbol> rhsRev = new ArrayList<FunctionSymbol>();
                rhsRev.addAll(rhs);
                Collections.reverse(rhsRev);
                rhs = ImmutableCreator.create(rhsRev);
            }

            final Matcher m = this.matcher.createPath(lhs.iterator());
            m.addRhs(rhs, signature);
        }
    }

    public CertificateGraph getCertificate(final Abortion abort) throws AbortionException, LimitExceededException {

        final CertificateGraph graph = new CertificateGraph();

        while (graph.doIteration()) {
            abort.checkAbortion();
        }

        return graph;
    }

    private ImmutableArrayList<FunctionSymbol> scanTerm(TRSTerm t) {
        final ArrayList<FunctionSymbol> l = new ArrayList<FunctionSymbol>();
        while (t != null && !t.isVariable()) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            l.add(f.getRootSymbol());
            assert f.getArguments().size() <= 1;
            if (f.getArguments().size() == 0) {
                t = null;
            } else {
                t = f.getArgument(0);
            }
        }
        return ImmutableCreator.create(l);
    }
}
