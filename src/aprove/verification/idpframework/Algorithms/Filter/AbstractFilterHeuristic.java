package aprove.verification.idpframework.Algorithms.Filter;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public abstract class AbstractFilterHeuristic implements IDPFilterHeuristic {

    protected static Logger log =
        Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter.AbstractFilterHeuristic");

    protected final Map<IDependencyGraph, Map<IFunctionSymbol<?>, ImmutableCollection<Integer>>> cache;
    protected final boolean filterRelations;

    @ParamsViaArgumentObject
    public AbstractFilterHeuristic(final Arguments arguments) {
        this.cache =
            new LinkedHashMap<IDependencyGraph, Map<IFunctionSymbol<?>, ImmutableCollection<Integer>>>();
        this.filterRelations = arguments.filterRelations;
    }

    @Override
    public ImmutableCollection<Integer> getFilteredPositions(final IDependencyGraph graph,
        final IFunctionSymbol<?> f) {
        final Map<IFunctionSymbol<?>, ImmutableCollection<Integer>> map =
            this.getMap(graph);
        return map.get(f);
    }

    protected Map<IFunctionSymbol<?>, ImmutableCollection<Integer>> getMap(final IDependencyGraph graph) {
        synchronized (this.cache) {
            Map<IFunctionSymbol<?>, ImmutableCollection<Integer>> map =
                this.cache.get(graph);
            if (map == null) {
                this.fillCache(graph);
                map = this.cache.get(graph);
            }
            return map;
        }
    }

    // FIXME!!!!
    protected void fillCache(final IDependencyGraph graph) {
        final IDPPredefinedMap predefinedMap = graph.getPredefinedMap();
        final CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>> activationMap =
            new CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>>();
        this.buildActivationMap(activationMap, graph);

        final ImmutableSet<IFunctionSymbol<?>> fss = graph.getFunctionSymbols();
        final Map<IFunctionSymbol<?>, boolean[]> usedPositions =
            new HashMap<IFunctionSymbol<?>, boolean[]>();
        for (final IFunctionSymbol<?> fs : fss) {
            usedPositions.put(fs, new boolean[fs.getArity()]);
        }

        this.initializeFilter(graph, usedPositions, activationMap);

        final Map<IFunctionSymbol<?>, ImmutableCollection<Integer>> res =
            new HashMap<IFunctionSymbol<?>, ImmutableCollection<Integer>>();
        int countFiltered = 0;
        int countUnfiltered = 0;
        for (final Map.Entry<IFunctionSymbol<?>, boolean[]> entry : usedPositions.entrySet()) {
            // do not filter pre-defined positions (in fact impossible by def.)
            if (PredefinedUtil.isPredefined(entry.getKey())) {
                res.put(entry.getKey(),
                    ImmutableCreator.create(Collections.<Integer> emptySet()));
            } else {
                final Set<Integer> filtered =
                    new LinkedHashSet<Integer>(entry.getKey().getArity());
                final boolean[] used = entry.getValue();
                for (int i = used.length - 1; i >= 0; i--) {
                    if (!used[i]) {
                        if (Globals.DEBUG_MPLUECKER) {
                            AbstractFilterHeuristic.log.finest("AbstractFilterHeuristic FILTER "
                                + entry.getKey() + "/" + i);
                        }
                        countFiltered++;
                        filtered.add(i);
                    } else {
                        countUnfiltered++;
                    }
                }
                res.put(entry.getKey(), ImmutableCreator.create(filtered));
            }
        }
        AbstractFilterHeuristic.log.fine("AbstractFilterHeuristic - FILTERED: " + countFiltered
            + " UNFILTERED: " + countUnfiltered);
        this.cache.put(graph, res);
    }

    private void buildActivationMap(final CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>> activationMap,
        final IDependencyGraph graph) {
        for (final Map.Entry<INode, ? extends ITerm<?>> nodeTerm : graph.getNodeMap().entrySet()) {
            this.buildActivationMap(activationMap, nodeTerm.getValue(),
                new ArrayList<ImmutablePair<IFunctionSymbol<?>, Integer>>());
        }
    }

    private void buildActivationMap(final CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>> activationMap,
        final ITerm<?> term,
        final ArrayList<ImmutablePair<IFunctionSymbol<?>, Integer>> pathToRoot) {
        if (!term.isVariable()) {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) term;
            final IFunctionSymbol<?> fs = fa.getRootSymbol();
            for (int i = 0; i < fs.getArity(); i++) {
                final ImmutablePair<IFunctionSymbol<?>, Integer> current =
                    new ImmutablePair<IFunctionSymbol<?>, Integer>(fs, i);
                activationMap.add(current, pathToRoot);
                if (!fa.getArgument(i).isVariable()) {
                    pathToRoot.add(current);
                    this.buildActivationMap(activationMap, fa.getArgument(i),
                        pathToRoot);
                    pathToRoot.remove(pathToRoot.size() - 1);
                }
            }
        }
    }

    private void buildActivationMap(final CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>> activationMap,
        final IDependencyGraph graph,
        final IEdge edge) {
        final CollectionMap<IVariable<?>, ImmutablePair<IFunctionSymbol<?>, Integer>> varPositions =
            new CollectionMap<IVariable<?>, ImmutablePair<IFunctionSymbol<?>, Integer>>();
        for (final ItpfConjClause clause : graph.getCondition(edge).getClauses()) {
            for (final ItpfAtom atom : clause.getLiterals().keySet()) {
                if (atom.isItp()) {
                    final ItpfItp itp = (ItpfItp) atom;
                    this.buildActivationMap(
                        activationMap,
                        itp.getL(),
                        new ArrayList<ImmutablePair<IFunctionSymbol<?>, Integer>>());
                    this.buildActivationMap(
                        activationMap,
                        itp.getR(),
                        new ArrayList<ImmutablePair<IFunctionSymbol<?>, Integer>>());
                    if (!itp.getL().isVariable()) {
                        this.extractVarPositions(varPositions,
                            (IFunctionApplication<?>) itp.getL());
                    }
                    if (!itp.getR().isVariable()) {
                        this.extractVarPositions(varPositions,
                            (IFunctionApplication<?>) itp.getR());
                    }
                }
            }
        }
        {
            final ITerm<?> fromTerm = graph.getTerm(edge.from);
            if (!fromTerm.isVariable()) {
                this.extractVarPositions(varPositions,
                    (IFunctionApplication<?>) fromTerm);
            }
        }
        {
            final ITerm<?> toTerm = graph.getTerm(edge.to);
            if (!toTerm.isVariable()) {
                this.extractVarPositions(varPositions, (IFunctionApplication<?>) toTerm);
            }
        }
        for (final Map.Entry<IVariable<?>, Collection<ImmutablePair<IFunctionSymbol<?>, Integer>>> varActivations : varPositions.entrySet()) {
            for (final ImmutablePair<IFunctionSymbol<?>, Integer> pos : varActivations.getValue()) {
                activationMap.add(pos, varActivations.getValue());
            }
        }
    }

    private void extractVarPositions(final CollectionMap<IVariable<?>, ImmutablePair<IFunctionSymbol<?>, Integer>> varPositions,
        final IFunctionApplication<?> fa) {
        for (final Map.Entry<IVariable<?>, List<IPosition>> vPos : fa.getVariablePositions().entrySet()) {
            for (final IPosition pos : vPos.getValue()) {
                final IPosition shorterPos = pos.shorten(1);
                final IFunctionApplication<?> subFa =
                    ((IFunctionApplication<?>) fa.getSubterm(shorterPos));
                final IFunctionSymbol<?> fs = subFa.getRootSymbol();
                varPositions.add(
                    (IVariable<?>) subFa.getArgument(pos.lastIndex()),
                    new ImmutablePair<IFunctionSymbol<?>, Integer>(fs,
                        pos.lastIndex()));
            }
        }
    }

    protected abstract void initializeFilter(IDependencyGraph graph,
        Map<IFunctionSymbol<?>, boolean[]> usedPositions,
        CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>> activationMap);

    protected void activatePosition(final IFunctionSymbol<?> fs,
        final int pos,
        final boolean promoteNonArithmetic,
        final Map<IFunctionSymbol<?>, boolean[]> usedPositions,
        final CollectionMap<ImmutablePair<IFunctionSymbol<?>, Integer>, ImmutablePair<IFunctionSymbol<?>, Integer>> activationMap) {
        final boolean[] used = usedPositions.get(fs);
        if (used[pos]) {
            return;
        }
        used[pos] = true;
        final PredefinedFunction<?, ?> func =
            PredefinedUtil.getPredefinedFunction(fs);
        if (promoteNonArithmetic || func == null || func.isArithmetic()) {
            final ImmutablePair<IFunctionSymbol<?>, Integer> key =
                new ImmutablePair<IFunctionSymbol<?>, Integer>(fs, pos);
            final Collection<ImmutablePair<IFunctionSymbol<?>, Integer>> activate =
                activationMap.get(key);
            if (activate != null) {
                for (final ImmutablePair<IFunctionSymbol<?>, Integer> newActive : activate) {
                    AbstractFilterHeuristic.log.finest("Activate " + fs + "/" + pos + " -> "
                        + newActive.x + "/" + newActive.y);
                    this.activatePosition(newActive.x, newActive.y,
                        promoteNonArithmetic, usedPositions, activationMap);
                }
            }
        }
    }

    public static class Arguments {
        public boolean filterRelations = true;
    }
}
