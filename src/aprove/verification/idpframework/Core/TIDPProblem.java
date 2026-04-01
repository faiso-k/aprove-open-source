package aprove.verification.idpframework.Core;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Processors.GraphProcessors.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class TIDPProblem extends IDPProblem {

    public static TIDPProblem create(final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap,
        final Collection<IRule> infRules,
        final Collection<IRule> rewriteRules,
        final IQTermSet q,
        final boolean minimal,
        final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph =
            new InitialGraphGenerator().createInitialGraph(itpfFactory,
                predefinedMap, infRules, rewriteRules, minimal, q, aborter);
        return TIDPProblem.create(graph, minimal);
    }

    public static TIDPProblem create(final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap,
        final Collection<IRule> rules,
        final IQTermSet q,
        final boolean minimal,
        final Abortion aborter) throws AbortionException {
        return TIDPProblem.create(itpfFactory, predefinedMap, rules, rules, q, minimal, aborter);
    }

    public static TIDPProblem create(final IDependencyGraph idpGraph,
        final ImmutableSet<IDPSubGraph> subGraphs,
        final boolean minimal) {
        return new TIDPProblem(idpGraph, subGraphs, minimal);
    }

    public static TIDPProblem create(final IDependencyGraph idpGraph,
        final boolean minimal) {
        final ImmutableSet<IDPSubGraph> subGraphs =
            ImmutableCreator.create(Collections.singleton(new IDPSubGraph(idpGraph.getEdges())));
        return TIDPProblem.create(idpGraph, subGraphs, minimal);
    }

    /**
     * Minimality flag.
     */
    private final boolean minimal;

    /**
     * Important subGraphs for termination analysis
     */
    protected final ImmutableSet<IDPSubGraph> subGraphs;


    protected TIDPProblem(final IDependencyGraph idpGraph,
        final ImmutableSet<IDPSubGraph> subGraphs,
        final boolean minimal) {
        super(idpGraph);

        this.subGraphs = subGraphs;
        this.minimal = minimal;

        if (Globals.useAssertions) {
            for (final IDPSubGraph scc : subGraphs) {
                for (final IDPSubGraph otherScc : subGraphs) {
                    if (!otherScc.equals(scc)) {
                        assert !scc.containsAll(otherScc) : "cleanup subgraphs";
                    }
                }
                assert idpGraph.getEdges().containsAll(scc.getEdges()) : "edge outside the graph";
            }
        }
    }

    public ImmutableSet<IDPSubGraph> getSubGraphs() {
        return this.subGraphs;
    }

    public boolean isMinimal() {
        return this.minimal;
    }

    @Override
    public TIDPProblem change(final IDependencyGraph idpGraph) {
        return this.change(idpGraph, null);
    }

    public TIDPProblem change(final IDependencyGraph idpGraph,
        final ImmutableSet<IDPSubGraph> subGraphs) {
        final IDependencyGraph newGraph =
            idpGraph != null ? idpGraph : this.idpGraph;

        final ImmutableSet<IDPSubGraph> newSccs = this.getNewSccs(newGraph, subGraphs);

        final TIDPProblem newIDP =
            new TIDPProblem(newGraph, newSccs, this.minimal);

        return newIDP;
    }

    private ImmutableSet<IDPSubGraph> getNewSccs(final IDependencyGraph newGraph,
        final ImmutableSet<IDPSubGraph> subGraphs) {
        ImmutableSet<IDPSubGraph> newSccs = subGraphs;
        if (newSccs == null) {
            final Set<IDPSubGraph> newSubGraphs = new LinkedHashSet<IDPSubGraph>();
            boolean changedSubGraphs = false;
            for (final IDPSubGraph subGraph : this.subGraphs) {
                if (newGraph.getEdges().containsAll(subGraph.getEdges())) {
                    newSubGraphs.add(subGraph);
                } else {
                    final LinkedHashSet<IEdge> newEdges = new LinkedHashSet<IEdge>(subGraph.getEdges());
                    newEdges.retainAll(newGraph.getEdges());
                    newSubGraphs.add(new IDPSubGraph(ImmutableCreator.create(newEdges)));
                    changedSubGraphs = true;
                }
            }

            if (changedSubGraphs) {
                newSccs = ImmutableCreator.create(newSubGraphs);
            } else {
                newSccs = this.subGraphs;
            }
        }
        return newSccs;
    }

    @Override
    public String toDOT() {
        return this.idpGraph.toDOT(this.subGraphs);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        super.export(sb, o, verbosityLevel);

        if (this.subGraphs.isEmpty()) {
            sb.append("No sub graphs must be considered for infinite loops.");
            sb.append(o.cond_linebreak());
        } else {
            sb.append("The following sub graphs must be considered for infinite loops:");
            sb.append(o.cond_linebreak());
            for (final IDPSubGraph subGraph : this.subGraphs) {
                sb.append(o.set(subGraph.getEdges(), Export_Util.NICE_SET));
                sb.append(o.cond_linebreak());
            }
        }
    }
}
