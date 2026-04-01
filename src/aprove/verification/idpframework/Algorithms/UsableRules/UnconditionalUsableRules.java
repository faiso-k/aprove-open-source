package aprove.verification.idpframework.Algorithms.UsableRules;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author MP
 */
public class UnconditionalUsableRules extends AbstractUsableRules {

    @Override
    protected ITerm<?> collectUsableRules(final IDPProblem idp,
        final Itpf precondition,
        final Set<ITerm<?>> sIntersection,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final ITerm<?> term,
        final List<ItpfQuantor> resultQuantifications, final LiteralMap resultUsableRules) {
        final IDependencyGraph graph = idp.getIdpGraph();

        if (term.isVariable()) {
            if (sIntersection.contains(term)) {
                return term;
            } else {
                return graph.getFreshVarGenerator().getFreshVariable((IVariable<?>) term, false);
            }
        } else {
            final IFunctionApplication<?> termFa = (IFunctionApplication<?>) term;
            final IFunctionSymbol<?> rootFs = termFa.getRootSymbol();
            final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(termFa.getRootSymbol().getArity());

            {   // fill new args and collect usable rule for deeper layers
                int i = 0;
                for (final ITerm<?> argTerm : termFa.getArguments()) {
                    final ITerm<?> cappedArgTerm = this.collectUsableRules(idp, precondition, sIntersection, relDependency, activeCondition.add(IActiveAtom.create(rootFs, i)), argTerm, resultQuantifications, resultUsableRules);
                    newArgs.add(cappedArgTerm);
                    i++;
                }
            }

            final IFunctionApplication<?> cappedTermFa = IFunctionApplication.create(termFa.getRootSymbol(), ImmutableCreator.create(newArgs));

            final Map<INode, Pair<VarRenaming, ISubstitution>> rootUnifyingNodes =
                graph.getRootUnifyingNodes(cappedTermFa, true);

            boolean hasRules = false;

            if (rootFs.isPredefined()) {
                final PredefinedFunction<?, ?> predefinedFunction = PredefinedUtil.getPredefinedFunction(rootFs);
                if (predefinedFunction != null && predefinedFunction.canMatchPredefLhs(cappedTermFa)) {
                    hasRules = true;
                }
            } else {
                for (final Entry<INode, Pair<VarRenaming, ISubstitution>> nodePositions : rootUnifyingNodes.entrySet()) {
                    final INode node = nodePositions.getKey();

                    final ImmutablePolyTermSubstitution nodeMgu =
                        ImmutableTermToPolyTermSubstitution.create(
                            nodePositions.getValue().y,
                            graph.getPredefinedMap(), graph.getPolyInterpretation());

                    final Pair<List<ItpfQuantor>, Set<ItpfImplication>> collectedRules =
                        this.collectUsableRules(
                            idp,
                            precondition,
                            relDependency,
                            activeCondition,
                            node,
                            nodeMgu,
                            new CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>>());

                    hasRules = hasRules || !collectedRules.y.isEmpty();

                    resultQuantifications.addAll(collectedRules.x);
                    resultUsableRules.putAll(collectedRules.y, true);
                }
            }

            if (hasRules) {
                return graph.getFreshVarGenerator().getFreshVariable("usableRules", cappedTermFa.getDomain(), false);
            } else {
                return cappedTermFa;
            }
        }
    }

    @Override
    protected Pair<List<ItpfQuantor>, Set<ItpfImplication>> collectUsableRules(final IDPProblem idp,
        final Itpf precondition,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final INode node,
        final ImmutablePolyTermSubstitution substitution,
        final CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>> visitedEdges) {

        if (Globals.useAssertions) {
            assert precondition.isTrue();
        }

        final IDependencyGraph graph = idp.getIdpGraph();

        final ImmutableMap<INode, ImmutableSet<IEdge>> successors =
            graph.getSuccessors(node);

        final List<ItpfQuantor> newQuantification =
            new ArrayList<ItpfQuantor>();
        final Set<ItpfImplication> result =
            new LinkedHashSet<ItpfImplication>();

        for (final ImmutableSet<IEdge> succEdges : successors.values()) {
            for (final IEdge succEdge : succEdges) {
                if (succEdge.type.isRewrite()) {
                    final Pair<List<ItpfQuantor>, Set<ItpfImplication>> edgeResult =
                        this.followEdge(idp, relDependency, activeCondition,
                            succEdge, substitution, visitedEdges);
                    newQuantification.addAll(edgeResult.x);
                    result.addAll(edgeResult.y);
                }
            }
        }

        return new Pair<List<ItpfQuantor>, Set<ItpfImplication>>(
            newQuantification, result);
    }

    @Override
    protected Pair<List<ItpfQuantor>, Set<ItpfImplication>> collectUsableRules(final IDPProblem idp,
        final Itpf precondition,
        final RelDependency relationalDependency,
        final IActiveCondition activeCondition,
        final IEdge edge,
        final ImmutablePolyTermSubstitution substitution,
        final CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>> visitedEdges) {
        if (Globals.useAssertions) {
            assert precondition.isTrue();
        }

        final Pair<List<ItpfQuantor>, Set<ItpfImplication>> edgeResult =
            this.followEdge(idp, relationalDependency, activeCondition, edge,
                substitution, visitedEdges);

        return edgeResult;
    }

    private Pair<List<ItpfQuantor>, Set<ItpfImplication>> followEdge(final IDPProblem idp,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final IEdge edge,
        final ImmutablePolyTermSubstitution substitution,
        final CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>> visitedEdges) {

        final IDependencyGraph graph = idp.getIdpGraph();

        final ITerm<?> fromTerm =
            graph.getTerm(edge.from).applySubstitution(substitution);

        final IActiveCondition fromActiveCondition =
            activeCondition.addAll(IActiveContext.create(fromTerm, edge.fromPos));

        final ImmutablePair<RelDependency, IActiveCondition> fromRelActive =
            new ImmutablePair<RelDependency, IActiveCondition>(relDependency,
                fromActiveCondition);

        if (visitedEdges.containsKey(edge.from)
            && visitedEdges.get(edge.from).contains(fromRelActive)) {
            // we have a fix point, complete
            return new Pair<List<ItpfQuantor>, Set<ItpfImplication>>(
                Collections.<ItpfQuantor> emptyList(),
                Collections.<ItpfImplication> emptySet());
        }

        visitedEdges.add(edge, fromRelActive);

        final ItpfFactory itpfFactory = idp.getItpfFactory();

        final LiteralMap conclusionLiterals = new LiteralMap();

        // add to result
        final ItpfEdgeOrientation orientationItp =
            itpfFactory.createEdgeOrientation(edge, null, RelDependency.Increasing,
                fromActiveCondition, substitution, substitution,
                EdgeOrientationRelation.ABSTRACT_GE);
        conclusionLiterals.put(orientationItp, true);

        final OutgoingEdgeGraph outgoingEdgeGraph =
            new OutgoingEdgeGraph(graph, edge.to);
        final Set<ItpfImplication> succesorUsableRules =
            new LinkedHashSet<ItpfImplication>();
        this.encodeSuccesorUsableRules(idp, relDependency, fromActiveCondition,
            outgoingEdgeGraph, outgoingEdgeGraph.getRoot(),
            graph.getTerm(edge.to), succesorUsableRules);
        conclusionLiterals.putAll(succesorUsableRules, true);

        final Itpf edgePreCondition =
            graph.getCondition(edge).applySubstitution(substitution);

        final Itpf conclusion =
            itpfFactory.create(itpfFactory.createClause(
                ImmutableCreator.create(conclusionLiterals), ITerm.EMPTY_SET));

        final ItpfImplication implication =
            itpfFactory.createImplication(edgePreCondition.getQuantorfree(), conclusion);

        final List<ItpfQuantor> quantifications =
            this.getQuantification(idp, edgePreCondition);
        quantifications.addAll(this.getQuantification(idp, conclusion));

        return new Pair<List<ItpfQuantor>, Set<ItpfImplication>>(
            quantifications, Collections.singleton(implication));
    }

    private List<ItpfQuantor> getQuantification(final IDPProblem idp,
        final Itpf edgePreCondition) {
        final PolyInterpretation<?> polyInterpretation =
            idp.getPolyInterpretation();
        final ItpfFactory itpfFactory = idp.getItpfFactory();

        final ImmutableSet<IVariable<?>> freeVariables =
            edgePreCondition.getFreeVariables();
        final ArrayList<ItpfQuantor> result =
            new ArrayList<ItpfQuantor>(freeVariables.size());

        for (final IVariable<?> freeVar : freeVariables) {
            if (!ItpfUtil.isQuantified(polyInterpretation,
                ItpfFactory.EMPTY_QUANTORS, freeVar)) {
                result.add(itpfFactory.createQuantor(true, freeVar));
            }
        }

        result.addAll(edgePreCondition.getQuantification());

        return result;
    }

    /**
     * @return set of URAs for deeper edges
     */
    private Set<ItpfEdgeUra> encodeSuccesorUsableRules(final IDPProblem idp,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final OutgoingEdgeGraph graph,
        final Node<Set<IEdge>> currentNode,
        final ITerm<?> term,
        final Set<ItpfImplication> result) {
        final Set<ItpfEdgeUra> deeperUras = new LinkedHashSet<ItpfEdgeUra>();

        final ItpfFactory itpfFactory = idp.getItpfFactory();

        for (final Edge<IPosition, Set<IEdge>> outEdge : graph.getOutEdges(currentNode)) {
            final IActiveCondition newActiveCondition =
                activeCondition.addAll(IActiveContext.create(term,
                    outEdge.getObject()));

            final Set<ItpfEdgeUra> subUras =
                this.encodeSuccesorUsableRules(idp, relDependency,
                    newActiveCondition, graph, outEdge.getEndNode(),
                    term.getSubterm(outEdge.getObject()), result);

            deeperUras.addAll(subUras);
        }

        final LiteralMap preconditionLiterals = new LiteralMap();
        preconditionLiterals.putAll(deeperUras, true);
        final Itpf precondition =
            itpfFactory.create(itpfFactory.createClause(
                ImmutableCreator.create(preconditionLiterals), ITerm.EMPTY_SET));

        for (final IEdge edge : currentNode.getObject()) {
            final ItpfEdgeUra edgeUra =
                itpfFactory.createEdgeUra(null, relDependency, activeCondition,
                    edge, ISubstitution.emptySubstitution(),
                    ItpRelation.ABSTRACT_GE);
            result.add(itpfFactory.createImplication(precondition,
                itpfFactory.create(edgeUra, true, ITerm.EMPTY_SET)));
            deeperUras.add(edgeUra);
        }

        return deeperUras;
    }

}