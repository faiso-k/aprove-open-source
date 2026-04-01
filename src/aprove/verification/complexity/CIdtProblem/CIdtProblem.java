package aprove.verification.complexity.CIdtProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class CIdtProblem extends IDPProblem {

    private final ImmutableSet<IEdge> S;
    private final ImmutableSet<IEdge> K;

    public static CIdtProblem create(final ItpfFactory itpfFactory,
        final IDPPredefinedMap predefinedMap,
        final Collection<IRule> infRules,
        final Collection<IRule> rewriteRules,
        final IQTermSet q,
        final Abortion aborter) throws AbortionException {

        final Pair<IDependencyGraph, ImmutableSet<IEdge>> initialProblem =
            new CIdtInitialGraphGenerator().createInitialComplexityGraph(itpfFactory,
                predefinedMap, infRules, rewriteRules, q, aborter);


        IDependencyGraph graph = initialProblem.x;
        ImmutableSet<IEdge> S = initialProblem.y;

        return CIdtProblem.create(graph, S, ImmutableCreator.create(new LinkedHashSet<IEdge>()));
    }

    public static CIdtProblem create(ItpfFactory itpfFactory,
        IDPPredefinedMap predefinedMap,
        Collection<IRule> rules,
        IQTermSet q,
        Abortion aborter) throws AbortionException {

        return CIdtProblem.create(itpfFactory, predefinedMap, rules, rules, q, aborter);
    }

    public static CIdtProblem create(IDependencyGraph idpGraph, ImmutableSet<IEdge> S, ImmutableSet<IEdge> K) {
        return new CIdtProblem(idpGraph, S, K);
    }

    protected CIdtProblem(IDependencyGraph idpGraph, ImmutableSet<IEdge> S, ImmutableSet<IEdge> K) {
        super("CIDT", "Complexity Integer DT Problem", idpGraph);
        this.checkConstrArguments(idpGraph, S, K);
        this.S = S;
        this.K = K;
    }

    private void checkConstrArguments(IDependencyGraph idpGraph,
        ImmutableSet<IEdge> S, ImmutableSet<IEdge> K) {

        if (Globals.useAssertions) {
            assert (idpGraph.getEdges().containsAll(S)) : "Graph doesn't contain some edge in S";
            for (IEdge edge : S) {
                assert (edge.type.isInf()) : "Edge type in S is not inf";
                assert (!K.contains(edge)) : "Edge of S is in K";
            }
            for (IEdge edge : K) {
                assert (edge.type.isInf()) : "Edge type in K is not inf";
                assert (!S.contains(edge)) : "Edge of K is in S";
            }

        }
    }

    @Override
    public CIdtProblem change(IDependencyGraph idpGraph) {
        return this.change(idpGraph, this.S, this.K);
    }

    public CIdtProblem change(ImmutableSet<IEdge> S) {
        return this.change(this.idpGraph, S, this.K);
    }

    public CIdtProblem change(IDependencyGraph idpGraph,
        final ImmutableSet<IEdge> S) {

        final CIdtProblem newProblem = new CIdtProblem(idpGraph, S, this.K);
        return newProblem;
    }

    public CIdtProblem change(IDependencyGraph idpGraph,
        final ImmutableSet<IEdge> S, final ImmutableSet<IEdge> K) {

        final CIdtProblem newProblem = new CIdtProblem(idpGraph, S, K);
        return newProblem;
    }

    @Override
    public String toDOT() {
        return this.idpGraph.toDOT();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {

        super.export(sb, o, verbosityLevel);
        sb.append("The set S contains the following edges:");
        sb.append(o.linebreak());
        sb.append(o.set(this.S, Export_Util.NICE_SET));
        sb.append(o.linebreak());
        sb.append(o.linebreak());

        sb.append("The set K contains the following edges:");
        sb.append(o.linebreak());
        sb.append(o.set(this.K, Export_Util.NICE_SET));
    }

    public ImmutableSet<IEdge> getS() {
        return this.S;
    }

    public static ImmutableSet<IEdge> cleanupS(IDependencyGraph newGraph, ImmutableSet<IEdge> S, ImmutableSet<IEdge> K) {

        Set<IEdge> newS = new LinkedHashSet<>();
        Set<IEdge> newK = new LinkedHashSet<>(K);

        Set<EdgeType> infTypes = new LinkedHashSet<>();
        infTypes.add(EdgeType.INF);
        infTypes.add(EdgeType.REWRITE_INF);

        for (IEdge edge : S) {
            if (newGraph.getEdges().contains(edge)) {
                if (newGraph.getInDegree(edge.from, infTypes) > 0) {
                    newS.add(edge);
                } else {
                    newK.add(edge);
                }
            }
        }
        for (IEdge edge : K) {
            if (!newGraph.getEdges().contains(edge)) {
                newK.remove(edge);
            }
        }

        return ImmutableCreator.create(newS);
    }

    public ImmutableSet<IEdge> getK() {
        return this.K;
    }
}
