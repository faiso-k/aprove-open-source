package aprove.verification.idpframework.Processors.Poly;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyRelationsEngine<R extends IntRing<R>> {

    private final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> emptyPolyMap;

    public PolyRelationsEngine() {
        this.emptyPolyMap = ImmutableCreator.create(Collections.<ImmutableMap<RelationNode<R>, BigInt>, R>emptyMap());
    }

    public Disjunction<RelationGraph<R>> getPolyRelations(final PolyInterpretation<R> polyInterpretation, final ItpfConjClause clause, final Abortion aborter) throws AbortionException {
        Set<RelationGraph<R>> relations = Collections.singleton(this.initRelations(polyInterpretation, clause));

        for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            if (literal.getKey().isPoly()) {
                final ItpfPolyAtom<R> poly = (ItpfPolyAtom<R>) literal.getKey();
                final Pair<Set<RelationGraph<R>>, Set<RelationEdge<R>>> addResult =
                    this.addPolyRelation(relations, poly, literal.getValue());
                relations = addResult.x;
            }
            aborter.checkAbortion();
        }

        return new Disjunction<RelationGraph<R>>(ImmutableCreator.create(relations));
    }

    protected ItpfConjClause getPolyFilteredClause(final ItpfFactory itpfFactory, final ItpfConjClause clause) {
        boolean changed = false;
        final LiteralMap normalizedLiterals = new LiteralMap();
        for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            if (literal.getKey().isPoly()) {
                normalizedLiterals.put(literal.getKey(), literal.getValue());
            } else {
                changed = true;
            }
        }

        if (changed || !clause.getS().isEmpty()) {
            ImmutableMap<ItpfAtom, Boolean> newLiterals;
            if (changed) {
                newLiterals = ImmutableCreator.create(normalizedLiterals);
            } else {
                newLiterals = clause.getLiterals();
            }

            return itpfFactory.createClause(newLiterals, ITerm.EMPTY_SET);
        } else {
            return clause;
        }
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    public Disjunction<RelationGraph<R>> getPropagatedPolyRelations(final PolyInterpretation<R> polyInterpretation, final ItpfConjClause clause, final Abortion aborter) throws AbortionException {
        final ItpfConjClause normalizedClause = this.getPolyFilteredClause(polyInterpretation.getConstraintFactory(), clause);

        final ImmutablePair<ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>, Disjunction<? extends RelationGraph<?>>> mark =
            normalizedClause.getMarks().getMark(PolyRelationsMark.MARK);

        if (mark != null) {
            return (Disjunction) mark.y;
        }

        Set<RelationGraph<R>> relations = Collections.singleton(this.initRelations(polyInterpretation, clause));

        final ArrayList<Map.Entry<ItpfAtom, Boolean>> sortedLiterals = new ArrayList<Map.Entry<ItpfAtom, Boolean>>(normalizedClause.getLiterals().entrySet());
        Collections.sort(sortedLiterals, LiteralComparator.INSTANCE);

        for (final Map.Entry<ItpfAtom, Boolean> literal : sortedLiterals) {
            final ItpfPolyAtom<R> poly = (ItpfPolyAtom<R>) literal.getKey();
            final Pair<Set<RelationGraph<R>>, Set<RelationEdge<R>>> addResult =
                this.addPolyRelation(relations, poly, literal.getValue());
            relations = addResult.x;
            final Set<RelationEdge<R>> newEdges = addResult.y;
            for (final RelationEdge<R> edge : newEdges) {
                final Set<RelationGraph<R>> propagatedRelations = new LinkedHashSet<RelationGraph<R>>();
                for (final RelationGraph<R> relationGraph : relations) {
                    this.relationPropagation(polyInterpretation, relationGraph, edge, aborter);

                    if (!relationGraph.isUnsat()) {
                        propagatedRelations.add(relationGraph);
                    }
                }
                relations = propagatedRelations;
            }
            aborter.checkAbortion();
        }

        for (final RelationGraph<R> relationGraph : relations) {
            this.expandKnownSignums(polyInterpretation.getRing(), relationGraph, aborter);
            relationGraph.freeze();
        }

        final Disjunction<RelationGraph<R>> result = new Disjunction<RelationGraph<R>>(ImmutableCreator.create(relations));

        normalizedClause.getMarks().setMark(
            PolyRelationsMark.MARK,
            normalizedClause.getSelfMark(),
            result);

        return result;
    }

    @SuppressWarnings("unchecked")
    private RelationGraph<R> initRelations(final PolyInterpretation<R> polyInterpretation,
        final ItpfConjClause clause) {
        final RelationGraph<R> result = new RelationGraph<R>(polyInterpretation.getRing());

        final R ring = polyInterpretation.getRing();
        for (final IVariable<?> var : clause.getVariables()) {
            if (var.getRing().isSameRing(ring)) {
                final IVariable<R> rVar = (IVariable<R>) var;
                result.addNode(new RelationNode<R>(rVar));
            }
        }

        return result;
    }

    private Pair<Set<RelationGraph<R>>, Set<RelationEdge<R>>> addPolyRelation(final Set<RelationGraph<R>> relations,
        final ItpfPolyAtom<R> poly, final Boolean literalPositive) {
        final Polynomial<R> positivePoly;
        final ConstraintType positiveContsraintType;

        if (literalPositive) {
            positivePoly = poly.getPoly();
            positiveContsraintType = poly.getConstraintType();
        } else {
            switch (poly.getConstraintType()) {
            case GE:
                positiveContsraintType = ConstraintType.GT;
                positivePoly = poly.getPoly().negate();
                break;
            case GT:
                positiveContsraintType = ConstraintType.GE;
                positivePoly = poly.getPoly().negate();
                break;
            case EQ:
                positiveContsraintType = ConstraintType.EQ;
                positivePoly = poly.getPoly();
                break;
            default:
                throw new UnsupportedOperationException("unknown constraint type");
            }
        }



        final Set<RelationGraph<R>> result = new LinkedHashSet<RelationGraph<R>>();
        final Set<RelationEdge<R>> newEdges = new LinkedHashSet<RelationEdge<R>>();

        for (final RelationGraph<R> relationGraph : relations) {
            RelationEdge<R> e;
            switch (positiveContsraintType) {
            case GE:
                e = this.addNormalizedPolyRelation(relationGraph, positivePoly);
                if (e != null) {
                    newEdges.add(e);
                }
                result.add(relationGraph);
                break;
            case GT:
                final Polynomial<R> normalizedPoly = positivePoly.subtract(poly.getInterpretation().getFactory().one(positivePoly.getRing()));
                e = this.addNormalizedPolyRelation(relationGraph, normalizedPoly);
                if (e != null) {
                    newEdges.add(e);
                }
                result.add(relationGraph);
                break;
            case EQ:
                if (literalPositive) {

                    e = this.addNormalizedPolyRelation(relationGraph, positivePoly);
                    if (e != null) {
                        newEdges.add(e);
                    }

                    e = this.addNormalizedPolyRelation(relationGraph, positivePoly.negate());
                    if (e != null) {
                        newEdges.add(e);
                    }

                    result.add(relationGraph);
                } else {
                    final RelationGraph<R> relationGraphGt = relationGraph;
                    final RelationGraph<R> relationGraphLt = relationGraph.clone();

                    final Polynomial<R> onePoly = poly.getInterpretation().getFactory().one(positivePoly.getRing());
                    final Polynomial<R> gtPoly = positivePoly.subtract(onePoly);
                    e = this.addNormalizedPolyRelation(relationGraphGt, gtPoly);
                    if (e != null) {
                        newEdges.add(e);
                    }

                    final Polynomial<R> ltPoly = positivePoly.negate().subtract(onePoly);
                    e = this.addNormalizedPolyRelation(relationGraphLt, ltPoly);
                    if (e != null) {
                        newEdges.add(e);
                    }

                    result.add(relationGraphGt);
                    result.add(relationGraphLt);
                }
                break;
            }
        }

        return new Pair<Set<RelationGraph<R>>, Set<RelationEdge<R>>>(result, newEdges);
    }

    /**
     * @return collection of new edges
     */
    private RelationEdge<R> addNormalizedPolyRelation(final RelationGraph<R> relationGraph,
        final Polynomial<R> normalizedPoly) {
        final Map<ImmutableMap<RelationNode<R>, BigInt>, R> edgeFrom = new LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R>();
        final Map<ImmutableMap<RelationNode<R>, BigInt>, R> edgeTo = new LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R>();

        R constantPart = normalizedPoly.getRing().zero();

        for (final Map.Entry<Monomial<R>, R> monomialCoeff : normalizedPoly.getMonomials().entrySet()) {
            final Monomial<R> monomial = monomialCoeff.getKey();
            final R coeff = monomialCoeff.getValue();

            if (!monomial.isConstantPart()) {
                final Map<RelationNode<R>, BigInt> expMap = new LinkedHashMap<RelationNode<R>, BigInt>();
                for (final Map.Entry<? extends PolyVariable<R>, BigInt> varExponent : monomial.getExponents().entrySet()) {
                    final PolyVariable<R> var = varExponent.getKey();
                    if (!var.isRealVar()) {
                        // no max variables
                        return null;
                    }

                    final IVariable<R> realVar = (IVariable<R>) var;
                    expMap.put(relationGraph.getOrAddNode(realVar),
                        varExponent.getValue());
                }

                if (coeff.signum() >= 0) {
                    edgeFrom.put(ImmutableCreator.create(expMap),
                        coeff);
                } else {
                    edgeTo.put(ImmutableCreator.create(expMap),
                        coeff.negate());
                }
            } else {
                constantPart = coeff;
            }
        }

        final RelationEdge<R> edge = new RelationEdge<R>(ImmutableCreator.create(edgeFrom),
                ImmutableCreator.create(edgeTo), constantPart.negate());

        if (relationGraph.addEdge(edge)) {
            return edge;
        } else {
            return null;
        }
    }

    public ItpfConjClause generateResultClause(final PolyInterpretation<R> polyInterpretation,
        final RelationGraph<R> relations) {
        return this.generateResultClause(polyInterpretation, relations.getEdges());
    }

    public ItpfConjClause generateResultClause(final PolyInterpretation<R> polyInterpretation,
        final Collection<RelationEdge<R>> edges) {
        final LiteralMap literals = new LiteralMap();

        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

        this.addRelationsToLiterals(polyInterpretation, edges, literals);

        return itpfFactory.createClause(ImmutableCreator.create(literals), ITerm.EMPTY_SET);
    }

    public ItpfFactory addRelationsToLiterals(final PolyInterpretation<R> polyInterpretation,
        final Collection<RelationEdge<R>> edges,
        final LiteralMap literals) {
        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();
        final PolyFactory polyFactory = polyInterpretation.getFactory();
        final R ring = polyInterpretation.getRing();
        final Set<RelationEdge<R>> equalityEdges = new HashSet<RelationEdge<R>>();

        for (final RelationEdge<R> edge : edges) {
            if (equalityEdges.contains(edge)) {
                continue;
            }

            final Map<Monomial<R>, R> polyMap = new LinkedHashMap<Monomial<R>, R>();

            for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoff : edge.from.entrySet()) {
                final Monomial<R> monomial = this.convertMonomial(ring, polyFactory, monomialCoff.getKey());
                polyMap.put(monomial, monomialCoff.getValue());
            }

            for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoff : edge.to.entrySet()) {
                final Monomial<R> monomial = this.convertMonomial(ring, polyFactory, monomialCoff.getKey());
                polyMap.put(monomial, monomialCoff.getValue().negate());
            }

            if (!edge.toOffset.isZero()) {
                polyMap.put(polyFactory.emptyMonomial(ring),
                    edge.toOffset.negate());
            }

            final RelationEdge<R> invertedEdge = edge.invert();
            final boolean isEquality = edges.contains(invertedEdge);

            if (isEquality) {
                equalityEdges.add(invertedEdge);
            }

            final ConstraintType constraintType = isEquality ? ConstraintType.EQ : ConstraintType.GE;

            final Polynomial<R> poly = polyFactory.create(ring, ImmutableCreator.create(polyMap));
            final ItpfPolyAtom<R> polyAtom = itpfFactory.createPoly(poly, constraintType, polyInterpretation);

            literals.put(polyAtom, true);
        }
        return itpfFactory;
    }

    private Monomial<R> convertMonomial(final R ring,
        final PolyFactory polyFactory,
        final ImmutableMap<RelationNode<R>, BigInt> mono) {
        final Map<PolyVariable<R>, BigInt> monomialMap = new LinkedHashMap<PolyVariable<R>, BigInt>();

        for (final Map.Entry<RelationNode<R>, BigInt> monoEntry : mono.entrySet()) {
            monomialMap.put(monoEntry.getKey().getVariable(), monoEntry.getValue());
        }

        return polyFactory.createMonomial(ring, ImmutableCreator.create(monomialMap));
    }

    public void relationPropagation(final PolyInterpretation<R> polyInterpretation,
        final RelationGraph<R> relationGraph,
        final Abortion aborter) throws AbortionException {
        // edge, edges used to transform the edge (avoid cycles)
        final List<RelationEdge<R>> edgesTodo = new ArrayList<RelationEdge<R>>(relationGraph.getEdges());

        for (final RelationEdge<R> edge : edgesTodo) {
            this.relationPropagation(polyInterpretation, relationGraph, edge, aborter);
        }
    }

    public void relationPropagation(final PolyInterpretation<R> polyInterpretation,
        final RelationGraph<R> relationGraph,
        final RelationEdge<R> edge,
        final Abortion aborter) throws AbortionException {

        if (relationGraph.contiansEdge(edge)) {
            this.expandEdge(relationGraph, edge, Collections.singleton(edge), aborter);
        }
    }

    public RelationGraph<R> extendClonedRelations(final PolyInterpretation<R> polyInterpretation,
        final RelationGraph<R> relations,
        final RelationGraph<R> extension,
        final Abortion aborter) throws AbortionException {
        final RelationGraph<R> clonedRelations = relations.clone();
        this.extendRelations(polyInterpretation, clonedRelations, extension, aborter);
        return clonedRelations;
    }

    public void extendRelations(final PolyInterpretation<R> polyInterpretation,
        final RelationGraph<R> relations,
        final RelationGraph<R> extension,
        final Abortion aborter) throws AbortionException {
        // edge, edges used to transform the edge (avoid cycles)
        final List<RelationEdge<R>> edgesTodo = new ArrayList<RelationEdge<R>>();

        for (final RelationEdge<R> edge : extension.getEdges()) {
            if (relations.addEdge(edge)) {
                edgesTodo.add(edge);
            }
        }

        for (final RelationEdge<R> edgeToDo : edgesTodo) {
            if (relations.contiansEdge(edgeToDo)) {
                this.expandEdge(relations, edgeToDo, Collections.singleton(edgeToDo), aborter);
            }
        }

        this.expandKnownSignums(polyInterpretation.getRing(), relations, aborter);
    }

    private void expandKnownSignums(final R ring, final RelationGraph<R> relations, final Abortion aborter) throws AbortionException {
        final ArrayList<RelationEdge<R>> edgesTodo = new ArrayList<RelationEdge<R>>(relations.getEdges());
        for (final RelationEdge<R> edge : edgesTodo) {
            this.expandKnownSignums(ring, relations, edge.from, aborter);
            this.expandKnownSignums(ring, relations, edge.to, aborter);
            aborter.checkAbortion();
        }
    }

    private void expandKnownSignums(final R ring,
        final RelationGraph<R> relations,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> polynomialMap,
        final Abortion aborter)
            throws AbortionException {
        for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialEntry : polynomialMap.entrySet()) {
            final ImmutableMap<RelationNode<R>, BigInt> expMap = monomialEntry.getKey();
            final Signum monomialSignum = Signum.getSignum(relations.getNodeSignums(), expMap);

            final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> monomialEntryMap =
                ImmutableCreator.create(Collections.singletonMap(expMap, ring.one()));

            if (monomialSignum.isPos()) {
                final R rhs = monomialSignum.isStrict() ? ring.one() : ring.zero();

                final RelationEdge<R> newEdge = new RelationEdge<R>(monomialEntryMap, this.emptyPolyMap, rhs);
                if (relations.addEdge(newEdge)) {
                    this.expandEdge(relations, newEdge, Collections.singleton(newEdge), aborter);
                }
            }

            if (monomialSignum.isNeg()) {
                final R rhs = monomialSignum.isStrict() ? ring.one() : ring.zero();

                final RelationEdge<R> newEdge = new RelationEdge<R>(this.emptyPolyMap, monomialEntryMap, rhs);
                if (relations.addEdge(newEdge)) {
                    this.expandEdge(relations, newEdge, Collections.singleton(newEdge), aborter);
                }
            }
        }
    }

    /**
     * @param aborter
     * @return true iff unsat edge was detected
     * @throws AbortionException
     */
    private boolean expandEdge(final RelationGraph<R> relations, final RelationEdge<R> edge, final Set<RelationEdge<R>> usedEdges, final Abortion aborter) throws AbortionException {
        final R ring = relations.getRing();
        {
            final LinkedHashSet<RelationEdge<R>> preMatchingCandidates = new LinkedHashSet<RelationEdge<R>>();
            for (final ImmutableMap<RelationNode<R>, BigInt> expMap : edge.from.keySet()) {
                for (final RelationNode<R> node : expMap.keySet()) {
                    preMatchingCandidates.addAll(relations.getPredecessors(node));
                }
                aborter.checkAbortion();
            }

            for (final RelationEdge<R> preMatchingCandidate : preMatchingCandidates) {
                final RelationEdge<R> combinedEdge = this.combineEdges(ring,
                    edge.from,
                    edge.to,
                    edge.toOffset,
                    preMatchingCandidate.to,
                    preMatchingCandidate.from,
                    preMatchingCandidate.toOffset,
                    false);


                aborter.checkAbortion();
                if (combinedEdge != null && relations.addEdge(combinedEdge)) {
                    if (combinedEdge.isUnsat()) {
                        return true;
                    }
                    final LinkedHashSet<RelationEdge<R>> extendedUsedEdges =
                        new LinkedHashSet<RelationEdge<R>>(usedEdges);
                    if (!extendedUsedEdges.add(preMatchingCandidate)) {
                        if (this.expandEdge(relations, combinedEdge, extendedUsedEdges, aborter)) {
                            return true;
                        }
                    }
                }
            }
        }

        {
            final LinkedHashSet<RelationEdge<R>> succMatchingCandidates = new LinkedHashSet<RelationEdge<R>>();
            for (final ImmutableMap<RelationNode<R>, BigInt> expMap : edge.to.keySet()) {
                for (final RelationNode<R> node : expMap.keySet()) {
                    succMatchingCandidates.addAll(relations.getSuccessors(node));
                }
                aborter.checkAbortion();
            }

            for (final RelationEdge<R> succMatchingCandidate : succMatchingCandidates) {
                final RelationEdge<R> combinedEdge = this.combineEdges(ring,
                    edge.to,
                    edge.from,
                    edge.toOffset,
                    succMatchingCandidate.from,
                    succMatchingCandidate.to,
                    succMatchingCandidate.toOffset,
                    true);

                aborter.checkAbortion();

                if (combinedEdge != null && relations.addEdge(combinedEdge)) {
                    if (combinedEdge.isUnsat()) {
                        return true;
                    }
                    final LinkedHashSet<RelationEdge<R>> extendedUsedEdges =
                        new LinkedHashSet<RelationEdge<R>>(usedEdges);
                    if (!extendedUsedEdges.add(succMatchingCandidate)) {
                        if (this.expandEdge(relations, combinedEdge, extendedUsedEdges, aborter)) {
                            return true;
                        }
                    }
                }
            }
        }

        return false;
    }

    private RelationEdge<R> combineEdges(final R ring,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> matched,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> other,
        final R toOffset,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> matching,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> replacement,
        final R machingToOffset,
        final boolean negateAll) {

        final R matchingFactor = this.getMatchingFactor(ring, matched, matching);
        if (matchingFactor != null) {
            final LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R> newEdgeFromPoly =
                new LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R>(matched);

            newEdgeFromPoly.keySet().removeAll(matching.keySet());

            for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoeff : other.entrySet()) {
                newEdgeFromPoly.put(monomialCoeff.getKey(), monomialCoeff.getValue().negate());
            }

            for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoeff : replacement.entrySet()) {
                final R factorCoeff = monomialCoeff.getValue().mult(matchingFactor);
                final R oldCoeff = newEdgeFromPoly.get(monomialCoeff.getKey());
                if (oldCoeff == null) {
                    newEdgeFromPoly.put(monomialCoeff.getKey(), factorCoeff);
                } else {
                    final R addedCoeff = oldCoeff.add(factorCoeff);
                    if (!addedCoeff.isZero()) {
                        newEdgeFromPoly.put(monomialCoeff.getKey(), addedCoeff);
                    } else {
                        newEdgeFromPoly.remove(monomialCoeff.getKey());
                    }
                }
            }

            final Iterator<Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R>> newEdgeFromIterator = newEdgeFromPoly.entrySet().iterator();
            final LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R> newEdgeToPoly =
                new LinkedHashMap<ImmutableMap<RelationNode<R>, BigInt>, R>();

            while(newEdgeFromIterator.hasNext()) {
                final Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoeff =
                    newEdgeFromIterator.next();
                R coeff = monomialCoeff.getValue();
                if (negateAll) {
                    coeff = coeff.negate();
                }
                if (coeff.signum() < 0) {
                    newEdgeFromIterator.remove();
                    newEdgeToPoly.put(monomialCoeff.getKey(), coeff.negate());
                } else if (negateAll) {
                    monomialCoeff.setValue(coeff);
                }
            }

            final R newEdgeToOffset = toOffset.add(machingToOffset.mult(matchingFactor));

            final RelationEdge<R> newEdge = new RelationEdge<R>(ImmutableCreator.create(newEdgeFromPoly),
                        ImmutableCreator.create(newEdgeToPoly), newEdgeToOffset);

            return newEdge;
        } else {
            return null;
        }
    }

    private R getMatchingFactor(final R ring, final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> poly,
        final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> matcher) {
        R factor = null;
        for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoeff : matcher.entrySet()) {
            final R polyCoeff = poly.get(monomialCoeff.getKey());
            if (polyCoeff == null) {
                return null;
            }
            final R matcherCoeff = monomialCoeff.getValue();

            if (!polyCoeff.mod(matcherCoeff).isZero()) {
                return null;
            }

            final R monomialFactor = polyCoeff.div(matcherCoeff);
            if (factor == null) {
                factor = monomialFactor;
            } else if (!factor.equals(monomialFactor)) {
                return null;
            }
        }

        if (factor == null) {
            factor = ring.one();
        }

        return factor;
    }

//    private Pair<Collection<RelationEdge<R>>, Collection<RelationEdge<R>>> followEdge(final PolyInterpretation<R> polyInterpretation,
//        final RelationGraph<R> relations,
//        final RelationEdge<R> edge,
//        final Set<RelationEdge<R>> usedEdges,
//        final Entry<ImmutableMap<RelationNode<R>, BigInt>, R> edgeTarget,
//        final RelationNode<R> targetVar,
//        final R coeff) {
//        final List<RelationEdge<R>> newEdges = new ArrayList<RelationEdge<R>>();
//        final List<RelationEdge<R>> newUsedEdges = new ArrayList<RelationEdge<R>>();
//
//        if (coeff.signum() < 0) {
//            final Map<ImmutableMap<RelationNode<R>, BigInt>, R> reducedEdgeTargets = new LinkedHashMap<ImmutableMap<RelationNode<R>,BigInt>, R>(edge.targets);
//            reducedEdgeTargets.remove(edgeTarget.getKey());
//
//            final Set<RelationEdge<R>> successors = relations.getSuccessors(targetVar);
//
//            succSearch : for (final RelationEdge<R> succ : successors) {
//                if (succ == edge || usedEdges.contains(succ)) {
//                    continue succSearch;
//                }
//
//                final Map<ImmutableMap<RelationNode<R>, BigInt>, R> newEdgeTargets = new LinkedHashMap<ImmutableMap<RelationNode<R>,BigInt>, R>(reducedEdgeTargets);
//                final R succCoeff = succ.targets.get(edgeTarget.getKey());
//
//                for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> preTarget : succ.targets.entrySet()) {
//                    if (!preTarget.equals(edgeTarget)) {
//                        final R targetCoeff = preTarget.getValue().mult(succCoeff);
//
//                        final R oldCoeff = newEdgeTargets.get(preTarget.getKey());
//                        if (oldCoeff == null) {
//                            newEdgeTargets.put(preTarget.getKey(), targetCoeff);
//                        } else {
//                            newEdgeTargets.put(preTarget.getKey(), targetCoeff.add(oldCoeff));
//                        }
//                    }
//                }
//
//                newUsedEdges.add(succ);
//                newEdges.add(new RelationEdge<R>(edge.from, ImmutableCreator.create(newEdgeTargets)));
//            }
//        }
//
//        final Set<RelationEdge<R>> predecessors = relations.getPredecessors(targetVar);
//
//        preSearch : for (final RelationEdge<R> pre : predecessors) {
//            if (pre == edge || usedEdges.contains(pre)) {
//                continue preSearch;
//            }
//
//            final Map<ImmutableMap<RelationNode<R>, BigInt>, R> newEdgeTargets = new LinkedHashMap<ImmutableMap<RelationNode<R>,BigInt>, R>(edge.targets);
//            final R preCoeff = pre.targets.get(edgeTarget.getKey());
//            if (preCoeff == null || coeff.signum() * preCoeff.signum() >= 0) {
//                continue preSearch;
//            }
//
//            if (!(coeff.getValue()).mod(preCoeff).isZero()) {
//                continue preSearch;
//            }
//
//            final R coeffFactor = coeff.getValue().div(preCoeff).negate();
//
//            for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> preTarget : pre.targets.entrySet()) {
//                if (!preTarget.equals(edgeTarget)) {
//                    final R targetCoeff = preTarget.getValue().mult(coeffFactor);
//
//                    final R oldCoeff = newEdgeTargets.get(preTarget.getKey());
//                    final R finalCoeff;
//                    if (oldCoeff == null) {
//                        finalCoeff = targetCoeff;
//                    } else {
//                        finalCoeff = targetCoeff.add(oldCoeff);
//                    }
//                    if (finalCoeff.isZero()) {
//                        newEdgeTargets.remove(preTarget.getKey());
//                    } else {
//                        newEdgeTargets.put(preTarget.getKey(), finalCoeff);
//                    }
//                }
//            }
//
//            R gcd = null;
//
//            for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> entry : newEdgeTargets.entrySet()) {
//                if (gcd == null) {
//                    gcd = entry.getValue();
//                } else {
//                    gcd = gcd.gcd(entry.getValue());
//                    if (gcd.isOne()) {
//                        break;
//                    }
//                }
//            }
//
//            if (gcd != null && !gcd.isOne()) {
//                for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> entry : newEdgeTargets.entrySet()) {
//                    entry.setValue(entry.getValue().div(gcd));
//                }
//            }
//
//            newUsedEdges.add(pre);
//            newEdges.add(new RelationEdge<R>(edge.from, ImmutableCreator.create(newEdgeTargets)));
//        }
//
//        if (newEdges.isEmpty()) {
//            return null;
//        } else {
//            return new Pair<Collection<RelationEdge<R>>, Collection<RelationEdge<R>>>(newEdges, newUsedEdges);
//        }
//    }

    private static class LiteralComparator implements Comparator<Map.Entry<ItpfAtom, Boolean>> {
        public static final LiteralComparator INSTANCE  = new LiteralComparator();

        @Override
        public int compare(final Entry<ItpfAtom, Boolean> o1, final Entry<ItpfAtom, Boolean> o2) {
            final ItpfPolyAtom<?> p1 = (ItpfPolyAtom<?>) o1.getKey();
            final ItpfPolyAtom<?> p2 = (ItpfPolyAtom<?>) o2.getKey();
            final boolean o1NegatedEquality = p1.getConstraintType() == ConstraintType.EQ && !o1.getValue();
            final boolean o2NegatedEquality = p2.getConstraintType() == ConstraintType.EQ && !o2.getValue();
            if (o1NegatedEquality) {
                if (o2NegatedEquality) {
                    return 0;
                } else {
                    return 1;
                }
            } else {
                if (o2NegatedEquality) {
                    return -1;
                } else {
                    return 0;
                }
            }
        }

    }
}
