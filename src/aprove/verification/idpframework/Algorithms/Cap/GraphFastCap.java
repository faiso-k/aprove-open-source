package aprove.verification.idpframework.Algorithms.Cap;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class GraphFastCap implements IGraphCap {

    @Override
    public <R extends SemiRing<R>> Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IEdge>>> cap(final IDependencyGraph graph,
        final Set<? extends ITerm<?>> s,
        final FreshVarGenerator freshVarGen,
        final ITerm<R> t,
        final boolean requireMatching) {
        final CollectionMap<IPosition, IEdge> resultPossibleApplications = new CollectionMap<IPosition, IEdge>();

        final ITerm<R> capResult = this.collectCap(graph, s, freshVarGen, IPosition.create(), t, requireMatching, resultPossibleApplications);

        return new Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IEdge>>>(capResult, this.convertMap(resultPossibleApplications));
    }

    private ImmutableMap<IPosition, ImmutableSet<IEdge>> convertMap(final CollectionMap<IPosition, IEdge> resultPossibleApplications) {
        final LinkedHashMap<IPosition, ImmutableSet<IEdge>> converted = new LinkedHashMap<IPosition, ImmutableSet<IEdge>>();

        for (final Map.Entry<IPosition, Collection<IEdge>> mapEntry : resultPossibleApplications.entrySet()) {
            converted.put(mapEntry.getKey(), ImmutableCreator.create((Set<IEdge>) mapEntry.getValue()));
        }

        return ImmutableCreator.create(converted);
    }

    public <R extends SemiRing<R>> ITerm<R> collectCap(final IDependencyGraph graph,
        final Set<? extends ITerm<?>> s,
        final FreshVarGenerator freshVarGen,
        final IPosition currentPosition,
        final ITerm<R> t,
        final boolean requireMatching,
        final CollectionMap<IPosition, IEdge> resultPossibleApplications) {
        final ITerm<R> cappedArgsTerm;

        if (t.isVariable()) {
            if (!s.contains(t)) {
                if (requireMatching) {
                    final ImmutableSet<INode> varRewritings = graph.getInitialRewriteNodes().get(null);
                    if (varRewritings != null) {
                        for (final INode initialNode : varRewritings) {
                            this.addApplicationsForNode(graph, currentPosition, resultPossibleApplications, initialNode);
                        }
                    }
                } else {
                    for (final ImmutableSet<INode> initialNodes : graph.getInitialRewriteNodes().values()) {
                        for (final INode initialNode : initialNodes) {
                            this.addApplicationsForNode(graph, currentPosition, resultPossibleApplications, initialNode);
                        }
                    }
                }
            }
            cappedArgsTerm = t;
        } else {
            final IFunctionApplication<R> termFa = (IFunctionApplication<R>) t;
            final IFunctionSymbol<R> rootFs = termFa.getRootSymbol();
            final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(termFa.getRootSymbol().getArity());

            {   // fill new args and collect usable rule for deeper layers
                int i = 0;
                for (final ITerm<?> argTerm : termFa.getArguments()) {
                    final ITerm<?> cappedArgTerm = this.collectCap(graph,
                        s,
                        freshVarGen,
                        currentPosition.append(i),
                        argTerm,
                        requireMatching,
                        resultPossibleApplications);
                    newArgs.add(cappedArgTerm);
                    i++;
                }
            }

            final IFunctionApplication<R> cappedArgsFa = IFunctionApplication.create(rootFs, ImmutableCreator.create(newArgs));
            cappedArgsTerm = cappedArgsFa;

            if (rootFs.isPredefined()) {
                final PredefinedFunction<?, ?> predefinedFunction = PredefinedUtil.getPredefinedFunction(rootFs);
                if (predefinedFunction != null && predefinedFunction.canMatchPredefLhs(cappedArgsFa)) {
                    resultPossibleApplications.add(currentPosition, Collections.<IEdge>singleton(null));
                }
            } else {
                final ImmutableSet<INode> possibleApplications = graph.getInitialRewriteNodes().get(cappedArgsFa.getRootSymbol());;
                if (possibleApplications != null) {
                    for (final INode node : possibleApplications) {
                        this.addApplicationsForNode(graph, currentPosition,
                            resultPossibleApplications, node);
                    }
                }
            }
        }

        if (resultPossibleApplications.containsKey(currentPosition)) {
            final IVariable<R> freshVar = freshVarGen.getFreshVariable("capX", t.getDomain(), false);
            return freshVar;
        } else {
            return cappedArgsTerm;
        }
    }

    private void addApplicationsForNode(final IDependencyGraph graph,
        final IPosition currentPosition,
        final CollectionMap<IPosition, IEdge> resultPossibleApplications,
        final INode node) {
        for (final Collection<IEdge> succEdges : graph.getSuccessors(node).values()) {
            for (final IEdge succEdge : succEdges) {
                if (succEdge.type.isRewrite()) {
                    resultPossibleApplications.add(currentPosition, succEdge);
                }
            }
        }
    }

    @Override
    public String getDescription() {
        return "FastGraphCap";
    }

    @Override
    public Estimation getEstimation() {
        return Estimation.FAST;
    }

}
