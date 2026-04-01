package aprove.verification.idpframework.Processors.Poly;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class RelationGraph<R extends SemiRing<R>> extends IDPExportable.IDPExportableSkeleton implements Cloneable, Freezable {

    private final Map<IVariable<R>, RelationNode<R>> varToNode;

    private final Map<RelationNode<R>, Signum> nodeToSignum;

    private final Set<RelationNode<R>> nodes;
    private final Set<RelationEdge<R>> edges;

    // contains a mapping from edge without constant -> edge
    private final Map<RelationEdge<R>, RelationEdge<R>> nonConstantEdges;

    private final Map<RelationEdge<R>, RelationEdge<R>> nonCoeffEdges;

    private final Map<RelationNode<R>, Set<RelationEdge<R>>> outEdges;
    private final Map<RelationNode<R>, Set<RelationEdge<R>>> inEdges;

    private final Set<RelationNode<R>> unmodifiableNodes;
    private final Set<RelationEdge<R>> unmodifiableEdges;
    private final Map<RelationNode<R>, Signum> unmodifiableNodeToSignum;

    private final R ring;

    private volatile boolean frozen;
    private volatile Boolean isUnsat;

    public RelationGraph(final R ring) {
        this.ring = ring;
        this.varToNode = new LinkedHashMap<IVariable<R>, RelationNode<R>>();
        this.nodeToSignum = new LinkedHashMap<RelationNode<R>, Signum>();
        this.unmodifiableNodeToSignum = Collections.unmodifiableMap(this.nodeToSignum);
        this.nodes = new LinkedHashSet<RelationNode<R>>();
        this.unmodifiableNodes = Collections.unmodifiableSet(this.nodes);
        this.edges = new LinkedHashSet<RelationEdge<R>>();
        this.unmodifiableEdges = Collections.unmodifiableSet(this.edges);
        this.nonConstantEdges = new HashMap<RelationEdge<R>, RelationEdge<R>>();
        this.nonCoeffEdges = new HashMap<RelationEdge<R>, RelationEdge<R>>();
        this.outEdges = new LinkedHashMap<RelationNode<R>, Set<RelationEdge<R>>>();
        this.inEdges = new LinkedHashMap<RelationNode<R>, Set<RelationEdge<R>>>();
    }

    @Override
    public void freeze() {
        this.frozen = true;
    }

    @Override
    public boolean isFrozen() {
        return this.frozen;
    }

    @Override
    public RelationGraph<R> clone() {
        final RelationGraph<R> clone = new RelationGraph<R>(this.ring);
        clone.varToNode.putAll(this.varToNode);
        clone.nodes.addAll(this.nodes);
        clone.edges.addAll(this.edges);
        clone.nonConstantEdges.putAll(this.nonConstantEdges);
        clone.nonCoeffEdges.putAll(this.nonCoeffEdges);
        clone.nodeToSignum.putAll(this.nodeToSignum);
        for (final Map.Entry<RelationNode<R>, Set<RelationEdge<R>>> entry : this.outEdges.entrySet()) {
            clone.outEdges.put(entry.getKey(), new LinkedHashSet<RelationEdge<R>>(entry.getValue()));
        }
        for (final Map.Entry<RelationNode<R>, Set<RelationEdge<R>>> entry : this.inEdges.entrySet()) {
            clone.inEdges.put(entry.getKey(), new LinkedHashSet<RelationEdge<R>>(entry.getValue()));
        }
        return clone;
    }

    public boolean isUnsat() {
        if (this.isUnsat == null) {
            synchronized(this) {
                if (this.isUnsat == null) {
                    return this.isUnsat = this.searchUnsatEdge(this.edges);
                }
            }
        }
        return this.isUnsat;
    }

    public boolean addNode(final RelationNode<R> node) {
        if (this.frozen) {
            throw new UnsupportedOperationException("graph is frozen");
        }
        if (this.nodes.add(node)) {
            if (node.getVariable() != null) {
                this.varToNode.put(node.getVariable(), node);
            }

            this.outEdges.put(node, new LinkedHashSet<RelationEdge<R>>());
            this.inEdges.put(node, new LinkedHashSet<RelationEdge<R>>());
            return true;
        } else {
            return false;
        }
    }

    public boolean addEdge(final RelationEdge<R> edge) {
        if (this.frozen) {
            throw new UnsupportedOperationException("graph is frozen");
        }
        final RelationEdge<R> nonConstantEdge = this.getNonConstantEdge(edge);
        final RelationEdge<R> nonCoeffEdge = this.getNonCoeffEdge(edge);
        {
            final RelationEdge<R> sameEdgeModuloConstant = this.nonConstantEdges.get(nonConstantEdge);
            if (sameEdgeModuloConstant != null) {

                final R edgeToOffset = edge.toOffset;
                final R sameEdgeToOffset = sameEdgeModuloConstant.toOffset;
                final boolean edgeSubsumed = edgeToOffset.semiCompareTo(sameEdgeToOffset) <= 0;

                if (edgeSubsumed) {
                    return false;
                } else {
                    this.removeEdge(sameEdgeModuloConstant);
                }
            }
        }

        {
            final RelationEdge<R> sameEdgeModuloCoeffs = this.nonCoeffEdges.get(nonCoeffEdge);
            if (sameEdgeModuloCoeffs != null) {
                return false;
            }
        }

        // search subsuming edge
        if (this.edges.add(edge)) {
            if ((this.isUnsat == null || !this.isUnsat)) {
                if (edge.isUnsat()) {
                    this.isUnsat = Boolean.TRUE;
                } else if (this.edges.contains(edge.invert()) && this.checkEqualityUnsatisfiable(edge)) {
                    this.isUnsat = Boolean.TRUE;
                }
            }

            this.addVarSignum(edge);

            this.nonConstantEdges.put(nonConstantEdge, edge);
            this.nonCoeffEdges.put(nonCoeffEdge, edge);

            this.linkEdge(edge, edge.from, this.outEdges);
            this.linkEdge(edge, edge.to, this.inEdges);
            return true;
        } else {
            return false;
        }
    }

    private boolean checkEqualityUnsatisfiable(final RelationEdge<R> edge) {
        if (this.ring instanceof BigInt) {
            BigInt coeff = null;
            boolean sameCoeff = true;
            EvenOdd coeffType = EvenOdd.UNKNOWN;

            final ArrayList<R> coeffs = new ArrayList<R>();
            coeffs.addAll(edge.from.values());
            coeffs.addAll(edge.to.values());

            for (final R c : coeffs) {
                final BigInt intC = (BigInt) c;
                if (coeff != null && !coeff.equals(intC)) {
                    sameCoeff = false;
                }
                coeff = intC;

                switch (coeffType) {
                case UNKNOWN:
                    coeffType = intC.isEven() ? EvenOdd.EVEN : EvenOdd.ODD;
                    break;
                case EVEN:
                    coeffType = intC.isEven() ? EvenOdd.EVEN : EvenOdd.WILD;
                    break;
                case ODD:
                    coeffType = !intC.isEven() ? EvenOdd.ODD : EvenOdd.WILD;
                    break;
                case WILD:
                }
            }

            final BigInt intToOffset = ((BigInt)edge.toOffset);
            return coeff != null && ((sameCoeff && !intToOffset.mod(coeff).isZero()) || (coeffType == EvenOdd.EVEN && !intToOffset.isEven()));
        } else {
            return false;
        }
    }


    private void addVarSignum(final RelationEdge<R> edge) {
        final Signum toOffsetSignum = Signum.getSignum(edge.toOffset);
        if (toOffsetSignum != null && toOffsetSignum.isPos()) {
            Pair<RelationNode<R>, R> nodeCoeff = null;
            if (edge.from.size() == 1) {
                if (edge.to.isEmpty()) {
                    nodeCoeff = this.getNodeCoeff(edge.from);
                }
            } else if (edge.from.isEmpty()) {
                if (edge.to.size() == 1) {
                    nodeCoeff = this.getNodeCoeff(edge.to);
                    if (nodeCoeff != null) {
                        nodeCoeff.y = nodeCoeff.y.negate();
                    }
                }
            }

            if (nodeCoeff != null) {
                final R coeff = nodeCoeff.y;
                final Signum signum = toOffsetSignum.isStrict() ? Signum.getSignum(coeff) : Signum.getSignum(coeff).makeNonStrict();
                if (signum != null) {
                    final Signum oldSignum = this.nodeToSignum.put(nodeCoeff.x, signum);
                    if (oldSignum != null) {
                        final Signum intersectedSignum = oldSignum.intersect(signum);
                        this.nodeToSignum.put(nodeCoeff.x, intersectedSignum);
                        if (intersectedSignum == Signum.Contradiction) {
                            this.isUnsat = true;
                        }
                    }
                }
            }
        }

    }

    private Pair<RelationNode<R>, R>  getNodeCoeff(final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> polyMap) {
        final Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialEntry =
            polyMap.entrySet().iterator().next();
        final ImmutableMap<RelationNode<R>, BigInt> expMap = monomialEntry.getKey();

        RelationNode<R> unknownNode = null;
        Signum currentSignum = Signum.StrictPos;
        for (final Map.Entry<RelationNode<R>, BigInt> nodeExp : expMap.entrySet()) {
            Signum nodeSignum = Signum.getSignum(this.nodeToSignum, nodeExp.getKey());
            if (nodeSignum == null) {
                nodeSignum = Signum.Unknown;
            }

            if (nodeSignum.isDetermined()) {
                if (nodeExp.getValue().isEven()) {
                    currentSignum = currentSignum.multEvenExponent(nodeSignum);
                } else {
                    currentSignum = currentSignum.mult(nodeSignum);
                }
            } else if (nodeExp.getValue().isEven()) {
                currentSignum = currentSignum.multEvenExponent(nodeSignum);
            } else {
                if (unknownNode == null) {
                    unknownNode = nodeExp.getKey();
                } else {
                    return null;
                }
            }

            if (!currentSignum.isDetermined() || !currentSignum.isStrict()) {
                return null;
            }
        }

        if (unknownNode != null) {
            if (currentSignum.isPos()) {
                return new Pair<RelationNode<R>, R>(unknownNode, monomialEntry.getValue());
            } else {
                return new Pair<RelationNode<R>, R>(unknownNode, monomialEntry.getValue().negate());
            }
        } else {
            return null;
        }
    }

    private boolean removeEdge(final RelationEdge<R> edge) {
        if (this.frozen) {
            throw new UnsupportedOperationException("graph is frozen");
        }
        if (this.edges.remove(edge)) {
            final RelationEdge<R> nonConstantEdge = this.getNonConstantEdge(edge);
            this.nonConstantEdges.remove(nonConstantEdge);

            final RelationEdge<R> nonCoeffEdge = this.getNonCoeffEdge(edge);
            this.nonCoeffEdges.remove(nonCoeffEdge);

            this.unlinkEdge(edge, edge.from, this.outEdges);
            this.unlinkEdge(edge, edge.to, this.inEdges);

            return true;
        } else {
            return false;
        }
    }

    public Set<RelationNode<R>> getNodes() {
        return this.unmodifiableNodes;
    }

    public Signum getNodeSignum(final RelationNode<R> node) {
        return this.nodeToSignum.get(node);
    }

    public Map<RelationNode<R>, Signum> getNodeSignums() {
        return this.unmodifiableNodeToSignum;
    }

    public boolean contiansEdge(final RelationEdge<R> edge) {
        return this.edges.contains(edge);
    }

    public Set<RelationEdge<R>> getEdges() {
        return this.unmodifiableEdges;
    }

    public RelationNode<R> getNode(final IVariable<R> var) {
        return this.varToNode.get(var);
    }

    public RelationNode<R> getOrAddNode(final IVariable<R> var) {
        RelationNode<R> node = this.varToNode.get(var);

        if (node == null) {
            node = new RelationNode<R>(var);
            this.addNode(node);
        }

        return node;
    }

    public Set<RelationEdge<R>> getSuccessors(final RelationNode<R> node) {
        return Collections.unmodifiableSet(this.outEdges.get(node));
    }

    public Set<RelationEdge<R>> getPredecessors(final RelationNode<R> node) {
        return Collections.unmodifiableSet(this.inEdges.get(node));
    }

    public R getRing() {
        return this.ring;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        for (final RelationEdge<R> edge : this.edges) {
            edge.export(sb, eu, verbosityLevel);
            sb.append(eu.linebreak());
        }
    }

    private void linkEdge(final RelationEdge<R> edge,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> polynom,
        final Map<RelationNode<R>, Set<RelationEdge<R>>> edgesMap) {
        for (final ImmutableMap<RelationNode<R>, BigInt> targetNodes : polynom.keySet()) {
            for (final RelationNode<R> targetNode : targetNodes.keySet()) {
                this.addNode(targetNode);
                edgesMap.get(targetNode).add(edge);
            }
        }
    }

    private void unlinkEdge(final RelationEdge<R> edge,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> polynom,
        final Map<RelationNode<R>, Set<RelationEdge<R>>> edgesMap) {
        for (final ImmutableMap<RelationNode<R>, BigInt> targetNodes : polynom.keySet()) {
            for (final RelationNode<R> targetNode : targetNodes.keySet()) {
                edgesMap.get(targetNode).remove(edge);
            }
        }
    }

    private RelationEdge<R> getNonConstantEdge(final RelationEdge<R> edge) {
        return new RelationEdge<R>(edge.from, edge.to, edge.toOffset.zero());
    }

    private RelationEdge<R> getNonCoeffEdge(final RelationEdge<R> edge) {
        final R one = this.ring.one();

        return new RelationEdge<R>(this.getNonCoeffMap(edge.from, one),
                this.getNonCoeffMap(edge.to, one),
                this.ring.zero());
    }

    private ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> getNonCoeffMap(final Map<ImmutableMap<RelationNode<R>, BigInt>, R> coeffMap,
        final R one) {
        final Map<ImmutableMap<RelationNode<R>, BigInt>, R> nonCoeffMap =
            new LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R>();

        for (final Entry<ImmutableMap<RelationNode<R>, BigInt>, R> entry : coeffMap.entrySet()) {
            nonCoeffMap.put(entry.getKey(), one);
        }
        return ImmutableCreator.create(nonCoeffMap);
    }

    private boolean searchUnsatEdge(final Set<RelationEdge<R>> edges) {
        for (final RelationEdge<R> edge : edges) {
            if (edge.isUnsat()) {
                return true;
            }
        }

        return false;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.edges.hashCode();
        result = prime * result + this.nodes.hashCode();
        return result;
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
        final RelationGraph<?> other = (RelationGraph<?>) obj;
        return this.nodes.equals(other.nodes) && this.edges.equals(other.edges);
    }

    private static enum EvenOdd {
        EVEN, ODD, UNKNOWN, WILD;
    }

}
