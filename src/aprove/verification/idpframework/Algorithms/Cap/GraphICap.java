package aprove.verification.idpframework.Algorithms.Cap;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
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
public class GraphICap implements IGraphCap {

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
        final IQTermSet q = graph.getQ();

        final ITerm<R> cappedArgsTerm;

        boolean hasRules = false;

        if (t.isVariable()) {
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

            cappedArgsTerm = IFunctionApplication.create(rootFs, ImmutableCreator.create(newArgs));

            if (rootFs.isPredefined()) {
                final PredefinedFunction<?, ?> predefinedFunction = PredefinedUtil.getPredefinedFunction(rootFs);
                if (predefinedFunction != null && predefinedFunction.canMatchPredefLhs(cappedArgsTerm)) {
                    hasRules = true;
                    resultPossibleApplications.add(currentPosition, Collections.<IEdge>singleton(null));
                }
            }
        }

        if (!hasRules) {
            final Map<INode, Pair<VarRenaming, ISubstitution>> possibleApplications;
            if (requireMatching) {
                possibleApplications = graph.getRootMatchingNodes(cappedArgsTerm, true);
            } else {
                possibleApplications = graph.getRootUnifyingNodes(cappedArgsTerm, true);
            }

            for (final Entry<INode, Pair<VarRenaming, ISubstitution>> matchingNodeApplications : possibleApplications.entrySet()) {

                final VarRenaming nodeRenaming = matchingNodeApplications.getValue().x;
                final ISubstitution mgu = matchingNodeApplications.getValue().y;

                final INode node = matchingNodeApplications.getKey();
                final ITerm<?> nodeTerm = graph.getTerm(node).applySubstitution(nodeRenaming);

                final ITerm<?> mguNodeTerm = nodeTerm.applySubstitution(mgu);

                if (this.isSNormalForm(s, q, mgu)) {
                    for (final Collection<IEdge> succEdges : graph.getSuccessors(matchingNodeApplications.getKey()).values()) {
                        for (final IEdge succEdge : succEdges) {
                            if (succEdge.type.isRewrite()) {
                                boolean possibleReduction = true;
                                final ITerm<?> redex = mguNodeTerm.getSubterm(succEdge.fromPos);
                                if (!redex.isVariable()) {
                                    final IFunctionApplication<?> redexFa =
                                        (IFunctionApplication<?>) redex;

                                    for (final ITerm<?> redexArg : redexFa.getArguments()) {
                                        if (q.canBeRewritten(redexArg)) {
                                            possibleReduction = false;
                                            break;
                                        }
                                    }
                                }

                                if (possibleReduction) {
                                    resultPossibleApplications.add(currentPosition, succEdge);
                                    hasRules = true;
                                }
                            }
                        }
                    }
                }
            }
        }

        if (hasRules) {
            final IVariable<R> freshVar = freshVarGen.getFreshVariable("capX", cappedArgsTerm.getDomain(), false);
            return freshVar;
        } else {
            return cappedArgsTerm;
        }
    }

    private boolean isSNormalForm(final Set<? extends ITerm<?>> s,
        final IQTermSet q,
        final ISubstitution sigma) {
        for (final ITerm<?> t : s) {
            if (q.canBeRewritten(t.applySubstitution(sigma))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String getDescription() {
        return "SimpleGraphCap";
    }

    @Override
    public Estimation getEstimation() {
        return Estimation.ICAP;
    }

}
