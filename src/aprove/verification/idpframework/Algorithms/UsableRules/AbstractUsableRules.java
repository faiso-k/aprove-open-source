package aprove.verification.idpframework.Algorithms.UsableRules;

import java.util.*;

import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
public abstract class AbstractUsableRules implements IUsableRulesEstimation {

    public AbstractUsableRules() {
        super();
    }

    @Override
    public IDPUsableRulesResult getUsableRules(final IDPProblem idp,
        final Itpf precondition,
        final RelDependency relDependency,
        final INode node,
        final ImmutablePolyTermSubstitution substitution) {

        final Pair<List<ItpfQuantor>, Set<ItpfImplication>> usableRules =
            this.collectUsableRules(
                idp,
                precondition,
                relDependency,
                IActiveCondition.EMPTY_CONDITION,
                node,
                substitution,
                new CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>>());

        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final LiteralMap literals = new LiteralMap(usableRules.y, true);

        return IDPUsableRulesResult.create(itpfFactory.create(
            ImmutableCreator.create(usableRules.x),
            itpfFactory.createClause(ImmutableCreator.create(literals), ITerm.EMPTY_SET)));
    }

    @Override
    public IDPUsableRulesResult getUsableRules(final IDPProblem idp,
        final Itpf precondition,
        final RelDependency relationalDependency,
        final IActiveCondition activeCondition,
        final IEdge edge,
        final ImmutablePolyTermSubstitution substitution) {

        final Pair<List<ItpfQuantor>, Set<ItpfImplication>> usableRules =
            this.collectUsableRules(
                idp,
                precondition,
                relationalDependency,
                activeCondition,
                edge,
                substitution,
                new CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>>());

        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final LiteralMap literals = new LiteralMap(usableRules.y, true);

        final ImmutableList<ItpfQuantor> mergedQuantification = ItpfUtil.mergeQuantors(precondition.getQuantification(), usableRules.x);

        return IDPUsableRulesResult.create(itpfFactory.create(
            mergedQuantification,
            itpfFactory.createClause(ImmutableCreator.create(literals), ITerm.EMPTY_SET)));
    }

    @Override
    public IDPUsableRulesResult getUsableRules(final IDPProblem idp,
        final Itpf precondition,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final ITerm<?> term) {

        final IDependencyGraph graph = idp.getIdpGraph();

        final List<ItpfQuantor> quantifications = new ArrayList<ItpfQuantor>();
        final LiteralMap usableRules =
            new LiteralMap();

        final Set<ITerm<?>> sIntersection = this.getSIntersection(precondition);

        this.collectUsableRules(idp, precondition, sIntersection, relDependency, activeCondition, term, quantifications, usableRules);

        final ItpfFactory itpfFactory = idp.getItpfFactory();
        return IDPUsableRulesResult.create(itpfFactory.create(
            ImmutableCreator.create(precondition.getQuantification()),
            itpfFactory.createClause(ImmutableCreator.create(usableRules), ITerm.EMPTY_SET)));
    }

    /**
     * @param sIntersection
     * @return capped term
     */
    protected abstract ITerm<?> collectUsableRules(final IDPProblem idp,
        final Itpf precondition,
        Set<ITerm<?>> sIntersection, final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final ITerm<?> term,
        final List<ItpfQuantor> resultQuantifications, final LiteralMap resultUsableRules);

    private Set<ITerm<?>> getSIntersection(final Itpf precondition) {
        if (precondition.getClauses().isEmpty()) {
            return Collections.emptySet();
        } else {
            final Iterator<ItpfConjClause> clausesIterator = precondition.getClauses().iterator();
            final LinkedHashSet<ITerm<?>> intersection = new LinkedHashSet<ITerm<?>>(clausesIterator.next().getS());

            while(clausesIterator.hasNext() && !intersection.isEmpty()) {
                intersection.retainAll(clausesIterator.next().getS());
            }

            return intersection;
        }
    }

    protected abstract Pair<List<ItpfQuantor>, Set<ItpfImplication>> collectUsableRules(final IDPProblem idp,
        Itpf precondition, final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final INode node,
        final ImmutablePolyTermSubstitution substitution,
        final CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>> visitedEdges);

    protected abstract Pair<List<ItpfQuantor>, Set<ItpfImplication>> collectUsableRules(IDPProblem idp,
        Itpf precondition,
        RelDependency relationalDependency,
        IActiveCondition activeCondition,
        IEdge edge,
        ImmutablePolyTermSubstitution substitution,
        CollectionMap<IEdge, ImmutablePair<RelDependency, IActiveCondition>> visitedEdges);
}