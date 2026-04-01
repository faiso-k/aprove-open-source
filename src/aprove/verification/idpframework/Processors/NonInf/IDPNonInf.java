package aprove.verification.idpframework.Processors.NonInf;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.idpframework.Processors.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.idpframework.Processors.NonInf.Solving.*;
import aprove.verification.idpframework.Processors.NonInf.Solving.ItpfPolyConstraintsSolver.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class IDPNonInf extends TIDPProcessor<Result> {

    private final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy;
    private final SolverType solverType;

    @ParamsViaArgumentObject
    public IDPNonInf(final Arguments arguments) {
        super("IDPNonInf");
        this.strategy = arguments.obtainStrategy();
        this.solverType = arguments.solver;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp,
        final Abortion aborter) throws AbortionException {

        final List<IDPNonInfSubGraphProof> subGraphProofs =
            new ArrayList<IDPNonInfSubGraphProof>();

        final Set<IDPSubGraph> newSubGraphs = new LinkedHashSet<IDPSubGraph>();

        final Set<IDPProblem> splittedIDPProblems = new LinkedHashSet<IDPProblem>();

        boolean success = false;

        for (final IDPSubGraph subGraph : idp.getSubGraphs()) {
            final SplitResult splitResult =
                this.splitSubGraph(idp, subGraph, aborter);
            if (splitResult != null) {
                final SubgraphSplitResult splitAndBoundSubgraph =
                    this.createNewSubGraphs(idp, subGraph, splitResult.strictEdges,
                        splitResult.boundEdges, this);
                newSubGraphs.addAll(splitAndBoundSubgraph.getNewSubGraphs());
                splittedIDPProblems.addAll(splitAndBoundSubgraph.getNewIDPProblems());

                subGraphProofs.add(new IDPNonInfSubGraphProof(subGraph,
                    splitResult, splitAndBoundSubgraph));
                success = true;
            } else {
                newSubGraphs.add(subGraph);
            }
        }

        if (success) {
            if (!newSubGraphs.isEmpty()) {
                final TIDPProblem newIDP =
                    idp.change(null, ImmutableCreator.create(GraphUtil.cleanupSubGraphs(newSubGraphs)));
                splittedIDPProblems.add(newIDP);
            }

            final IDPNonInfProof proof =
                new IDPNonInfProof(ImmutableCreator.create(subGraphProofs));

            return ResultFactory.provedAnd(splittedIDPProblems, YNMImplication.SOUND, proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private SubgraphSplitResult createNewSubGraphs(
        final TIDPProblem idp,
        final IDPSubGraph subGraph,
        final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> strictEdges,
        final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> boundEdges, final Mark<? extends Result> processorMark) {

        final Map<IEdge, Collection<ItpfConjClause>> strictAndBoundIntersection =
            this.getStrictAndBoundIntersection(strictEdges, boundEdges);

        if (!strictAndBoundIntersection.isEmpty()) {
            return this.createSplitResult(idp, subGraph, strictAndBoundIntersection, processorMark);
        } else {
            final SubgraphSplitResult splitStrict = this.createSplitResult(idp, subGraph, strictEdges, processorMark);
            final SubgraphSplitResult splitBound = this.createSplitResult(idp, subGraph, boundEdges, processorMark);

            final Set<IDPSubGraph> newSubGraphs = new LinkedHashSet<IDPSubGraph>(splitStrict.getNewSubGraphs());
            newSubGraphs.addAll(splitBound.getNewSubGraphs());

            final Set<IDPProblem> newIDPProblems = new LinkedHashSet<IDPProblem>(splitStrict.getNewIDPProblems());
            newIDPProblems.addAll(splitBound.getNewIDPProblems());

            return new SubgraphSplitResult(ImmutableCreator.create(newSubGraphs), ImmutableCreator.create(newIDPProblems));
        }
    }

    private SubgraphSplitResult createSplitResult(final TIDPProblem idp, final IDPSubGraph subGraph,
        final Map<IEdge, ? extends Collection<ItpfConjClause>> removedClauses, final Mark<? extends Result> processorMark) {
        final IDependencyGraph graph = idp.getIdpGraph();
        final ItpfFactory itpfFactory = idp.getItpfFactory();

        final Set<IEdge> newSubGraph = new LinkedHashSet<IEdge>();
        final EdgeConditionMap newConditions = new EdgeConditionMap(itpfFactory, graph.getFreshVarGenerator());

        for (final IEdge edge : subGraph.getEdges()) {
            final Collection<ItpfConjClause> removed = removedClauses.get(edge);
            if (removed != null && !removed.isEmpty()) {
                final Itpf edgeCondition = graph.getCondition(edge);
                final LinkedHashSet<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>(edgeCondition.getClauses());
                newClauses.removeAll(removed);
                if (!newClauses.isEmpty()) {
                    newSubGraph.add(edge);
                    newConditions.putOr(edge, itpfFactory.create(edgeCondition.getQuantification(), ImmutableCreator.create(newClauses)));
                }
            } else {
                newSubGraph.add(edge);
            }
        }

        if (newSubGraph.isEmpty()) {
            return new SubgraphSplitResult(ImmutableCreator.create(Collections.<IDPSubGraph>emptySet()),
                ImmutableCreator.create(Collections.<IDPProblem>emptySet()));
        } else {
            final IDPSubGraph newIDPSubGraph = new IDPSubGraph(ImmutableCreator.create(newSubGraph));
            if (newConditions.isEmpty()) {
                return new SubgraphSplitResult(ImmutableCreator.create(Collections.singleton(newIDPSubGraph)),
                    ImmutableCreator.create(Collections.<IDPProblem>emptySet()));
            } else {
                final IDependencyGraph newGraph = graph.change(null, newConditions.getMap(), null, null, null, processorMark);

                final IDPProblem newIDP =
                    idp.change(newGraph, ImmutableCreator.create(Collections.singleton(newIDPSubGraph)));

                return new SubgraphSplitResult(ImmutableCreator.create(Collections.<IDPSubGraph>emptySet()),
                    ImmutableCreator.create(Collections.singleton(newIDP)));
            }
        }
    }

    private Map<IEdge, Collection<ItpfConjClause>> getStrictAndBoundIntersection(final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> strictEdges,
        final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> boundEdges) {
        final Map<IEdge, Collection<ItpfConjClause>> intersection = new LinkedHashMap<IEdge, Collection<ItpfConjClause>>();
        for (final Map.Entry<IEdge, ImmutableCollection<ItpfConjClause>> strictEntry : strictEdges.entrySet()) {
            final ImmutableCollection<ItpfConjClause> boundClauses = boundEdges.get(strictEntry.getKey());
            if (boundClauses != null) {
                final LinkedHashSet<ItpfConjClause> clauseIntersection =
                    new LinkedHashSet<ItpfConjClause>(boundClauses);
                clauseIntersection.retainAll(strictEntry.getValue());
                if (!clauseIntersection.isEmpty()) {
                    intersection.put(strictEntry.getKey(), clauseIntersection);
                }
            }
        }

        return intersection;
    }

    private SplitResult splitSubGraph(final IDPProblem idp,
        final IDPSubGraph scc,
        final Abortion aborter) throws AbortionException {

        final NonInfImplicationGraph implicationGraph =
            new NonInfImplicationGraph(idp, scc);
        final CollectionMap<Itpf, IEdge> implications =
            implicationGraph.getImplications();

        final Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications =
            this.processEdgeImplications(idp, implicationGraph, implications,
                aborter);

        final Conjunction<Itpf> constraints =
            this.createConstraints(idp, simplifiedImplications, scc, aborter);

        final ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> sideConstraints =
            this.createSideConstraints(idp, constraints, scc, aborter);

        final LinkedHashSet<Itpf> totalConstraints = new LinkedHashSet<Itpf>(constraints.asCollection());
        totalConstraints.addAll(sideConstraints.x.asCollection());


        PolyInterpretation<BigInt> solution = null;
        try {
            solution = this.solveConstraints(idp, new Conjunction<Itpf>(ImmutableCreator.create(totalConstraints)), aborter);
        } catch (final Exception e) {
            e.printStackTrace();
        }

        if (solution != null) {
            final Pair<ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>, ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>> strictAndBound =
                this.getStrictAndBoundEdges(idp, implicationGraph, solution);

            strictAndBound.x.isEmpty();

            return new SplitResult(solution, strictAndBound.x,
                strictAndBound.y, ImmutableCreator.create(simplifiedImplications), sideConstraints);
        } else {
            if (Globals.DEBUG_MPLUECKER) {
                System.err.println("FAILED SOLVING: ");
                for (final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof : simplifiedImplications.keySet()) {
                    System.err.println(proof);
                }
                for (final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof : sideConstraints.y.values()) {
                    System.err.println(proof);
                }
            }
            return null;
        }
    }

    private Conjunction<Itpf> createConstraints(final IDPProblem idp,
        final Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications,
        final IDPSubGraph scc,
        final Abortion aborter) {
        final Set<Itpf> simplifiedConstraints = new LinkedHashSet<Itpf>();

        for (final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof : simplifiedImplications.keySet()) {
            simplifiedConstraints.addAll(proof.getLastFormulaStates());
        }

        return new Conjunction<Itpf>(
            ImmutableCreator.create(simplifiedConstraints));
    }

    private ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> createSideConstraints(final IDPProblem idp,
        final Conjunction<Itpf> simplifiedConstraints,
        final IDPSubGraph scc,
        final Abortion aborter) throws AbortionException {

        final Set<Itpf> simplifiedSideConstraints = new LinkedHashSet<Itpf>();

        // add side constraints
        simplifiedSideConstraints.add(this.getAtLeastOneConstraint(idp, scc,
            ConstantType.StrictOrientation));
        simplifiedSideConstraints.add(this.getAtLeastOneConstraint(idp, scc,
            ConstantType.BoundOrientation));

        final Map<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> sideConsraintProofs =
            this.getSimplifiedSideConstraints(idp, simplifiedConstraints, aborter);

        for (final Map.Entry<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> varProof : sideConsraintProofs.entrySet()) {
            simplifiedSideConstraints.addAll(varProof.getValue().getLastFormulaStates());
        }

        return new ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>>(
            new Conjunction<Itpf>(
                ImmutableCreator.create(simplifiedSideConstraints)),
            ImmutableCreator.create(sideConsraintProofs));
    }

    private Map<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> getSimplifiedSideConstraints(final IDPProblem idp,
        final Conjunction<Itpf> simplifiedConstraints,
        final Abortion aborter) throws AbortionException {

        final Set<IVariable<?>> usedVariables = this.collectVariables(simplifiedConstraints);

        return idp.getIdpGraph().getSideConstraints().getSideConstraints(idp, usedVariables, aborter);
    }

    private Set<IVariable<?>> collectVariables(final Iterable<Itpf> simplifiedConstraints) {
        final LinkedHashSet<IVariable<?>> variables =
            new LinkedHashSet<IVariable<?>>();
        for (final Itpf formula : simplifiedConstraints) {
            variables.addAll(formula.getVariables());
        }
        return variables;
    }

    private Itpf getAtLeastOneConstraint(final IDPProblem idp,
        final IDPSubGraph scc,
        final ConstantType constantType) {
        final PolyInterpretation<?> interpretation =
            idp.getIdpGraph().getPolyInterpretation();
        final Set<ItpfConjClause> clauses = new LinkedHashSet<ItpfConjClause>();

        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final IDependencyGraph graph = idp.getIdpGraph();

        for (final IEdge edge : scc.getEdges()) {
            for (final ItpfConjClause conditionClause : graph.getCondition(edge)) {
                final ItpfBoolPolyVar<?> var =
                    interpretation.getItpfBooleanPolyVar(constantType, edge, conditionClause, Collections.<Itpf>emptySet());

                clauses.add(itpfFactory.createClause(var, Boolean.TRUE,
                    ITerm.EMPTY_SET));
            }
        }

        return itpfFactory.create(ImmutableCreator.create(clauses));
    }

    private Pair<ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>, ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>> getStrictAndBoundEdges(final IDPProblem idp,
        final NonInfImplicationGraph implicationGraph,
        final PolyInterpretation<BigInt> solution) {
        final CollectionMap<IEdge, ItpfConjClause> strictOrientation = new CollectionMap<IEdge, ItpfConjClause>();
        final CollectionMap<IEdge, ItpfConjClause> boundOrientation = new CollectionMap<IEdge, ItpfConjClause>();

        final IDependencyGraph graph = idp.getIdpGraph();
        for (final IEdge edge : implicationGraph.getSubGraph().getEdges()) {
            for (final ItpfConjClause conditionClause : graph.getCondition(edge)) {

                final BigInt strictValue =
                    solution.getBooleanPolyVarValue(ConstantType.StrictOrientation,
                        edge, conditionClause, Collections.<Itpf>emptySet());
                if (strictValue != null && strictValue.isOne()) {
                    strictOrientation.add(edge, conditionClause);
                }
                final BigInt boundValue =
                    solution.getBooleanPolyVarValue(ConstantType.BoundOrientation,
                        edge, conditionClause, Collections.<Itpf>emptySet());

                if (boundValue != null && boundValue.isOne()) {
                    boundOrientation.add(edge, conditionClause);
                }
            }
        }

        final Pair<ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>, ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>> strictAndBound =
            new Pair<ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>, ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>>(this.makeImmutable(strictOrientation),
                    this.makeImmutable(boundOrientation));
        return strictAndBound;
    }

    private ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> makeImmutable(final CollectionMap<IEdge, ItpfConjClause> map) {
        final Map<IEdge, ImmutableCollection<ItpfConjClause>> result = new LinkedHashMap<IEdge, ImmutableCollection<ItpfConjClause>>();
        for (final Map.Entry<IEdge, Collection<ItpfConjClause>> entry : map.entrySet()) {
            result.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }

        return ImmutableCreator.create(result);
    }

    private PolyInterpretation<BigInt> solveConstraints(final IDPProblem idp,
        final Conjunction<Itpf> constraints,
        final Abortion aborter) throws AbortionException {

        final ItpfPolyConstraintsSolver solver =
            this.solverType.getSolver();

        try {
            final PolyInterpretation<BigInt> solution =
                solver.solve(
                    idp.getPredefinedMap(),
                    (PolyInterpretation<BigInt>) idp.getIdpGraph().getPolyInterpretation(),
                    constraints, aborter);
            return solution;
        } catch (final Exception e) {
            e.printStackTrace();
            return null;
        }
    }

    private Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> processEdgeImplications(final IDPProblem idp,
        final NonInfImplicationGraph implicationGraph,
        final CollectionMap<Itpf, IEdge> implications,
        final Abortion aborter) throws AbortionException {
        final List<ItpfSchedulerEdgesExecutorData> workers =
            new ArrayList<ItpfSchedulerEdgesExecutorData>(
                implicationGraph.getImplications().size());

        for (final Map.Entry<Itpf, Collection<IEdge>> implication : implicationGraph.getImplications().entrySet()) {
            workers.add(new ItpfSchedulerEdgesExecutorData(idp,
                implication.getKey(), implication.getValue(), this.strategy,
                ImplicationType.COMPLETE, aborter));
        }

        try {
            MultithreadedExecutor.execute(workers, aborter);
        } catch (final Exception e) {
            e.printStackTrace();
        }

        final Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> implicationProofs =
            new LinkedHashMap<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>>();

        for (final ItpfSchedulerEdgesExecutorData worker : workers) {
            implicationProofs.put(worker.getProof(),
                ImmutableCreator.create(new LinkedHashSet<IEdge>(
                    worker.getEdges())));
        }

        return implicationProofs;
    }

    public static class Arguments {

        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> obtainStrategy() {
            return ItpfStrategy.DefaultStrategy.getStrategy();
        }

        public SolverType solver = SolverType.SAT_SOLVER;

    }

    public class IDPNonInfProof extends DefaultProof {

        private final ImmutableList<IDPNonInfSubGraphProof> subProofs;

        public IDPNonInfProof(
                final ImmutableList<IDPNonInfSubGraphProof> subProofs) {
            this.subProofs = subProofs;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();

            final Iterator<IDPNonInfSubGraphProof> subProofIterator =
                this.subProofs.iterator();

            while (subProofIterator.hasNext()) {
                subProofIterator.next().export(sb, o, level);
                if (subProofIterator.hasNext()) {
                    sb.append(o.linebreak());
                    sb.append(o.linebreak());
                    sb.append(o.linebreak());
                }
            }

            return sb.toString();
        }

    }

    public static class IDPNonInfSubGraphProof extends IDPExportable.IDPExportableSkeleton {

        private final IDPSubGraph subGraph;
        private final SplitResult splitResult;
        private final SubgraphSplitResult splitGraphs;

        public IDPNonInfSubGraphProof(final IDPSubGraph subGraph,
                final SplitResult splitResult,
                final SubgraphSplitResult splitAndBoundSubgraph) {
            this.subGraph = subGraph;
            this.splitResult = splitResult;
            this.splitGraphs = splitAndBoundSubgraph;
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            this.exportSplit(sb, eu, verbosityLevel);

            sb.append(eu.linebreak());

            this.exportStrictAndBound(sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            sb.append("The following polynomial interpretation has been used:");
            sb.append(eu.linebreak());
            this.splitResult.solvingInterpretation.export(sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            sb.append("The following nat / int domain decisions were made:");
            sb.append(eu.linebreak());
            this.exportNatIntDomains(sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            final StringBuilder detailedImplicationProofs = new StringBuilder();
            final StringBuilder detailedSideConstraintProofs = new StringBuilder();

            Map<Itpf, Integer> finalEquationsToId;
            if (verbosityLevel.compareTo(VerbosityLevel.MIDDLE) >= 0) {
                finalEquationsToId =
                    this.exportImplicationProofs(detailedImplicationProofs, eu,
                        verbosityLevel);
                finalEquationsToId.putAll(this.exportSideConstraintProofs(detailedSideConstraintProofs, finalEquationsToId, eu,
                        verbosityLevel));
            } else {
                finalEquationsToId = Collections.<Itpf, Integer> emptyMap();
            }

            this.exportConstraintSummary(finalEquationsToId, sb, eu, verbosityLevel);
            sb.append(eu.linebreak());
            this.exportSideConstraintSummary(finalEquationsToId, sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            if (verbosityLevel.compareTo(VerbosityLevel.MIDDLE) >= 0) {
                sb.append(detailedImplicationProofs);
                sb.append(eu.linebreak());
                sb.append(detailedSideConstraintProofs);
            }

        }

        private void exportNatIntDomains(final StringBuilder sb, final Export_Util eu, final VerbosityLevel verbosityLevel) {
            final Map<ItpfBoolPolyVar<BigInt>, BigInt> natDomainVars = this.splitResult.solvingInterpretation.getUsedBooleanPolyVarValues(ConstantType.NatDomain);
            for (final Map.Entry<ItpfBoolPolyVar<BigInt>, BigInt> natVar : natDomainVars.entrySet()) {
                if (natVar.getValue() != null) {
                    natVar.getKey().getPolyVar().export(sb, eu, VerbosityLevel.LOW);
                    sb.append(" = ");
                    natVar.getValue().export(sb, eu, VerbosityLevel.LOW);
                    if (natVar.getValue().isZero()) {
                        sb.append(" (int)");
                    } else {
                        sb.append(" (nat)");
                    }
                    sb.append(eu.linebreak());
                }
            }
        }

        private void exportSplit(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The sub graph");
            sb.append(eu.linebreak());
            this.subGraph.export(sb, eu, verbosityLevel);
            sb.append(eu.linebreak());
            if (!this.splitGraphs.getNewSubGraphs().isEmpty()) {
                sb.append("has been ");
                if (this.splitGraphs.getNewSubGraphs().size() > 1) {
                    sb.append("split into the following graphs:");
                } else {
                    sb.append("replaced by the following graph:");
                }
                sb.append(eu.linebreak());

                for (final IDPSubGraph splitGraph : this.splitGraphs.getNewSubGraphs()) {
                    splitGraph.export(sb, eu, verbosityLevel);
                    sb.append(eu.linebreak());
                }

                if (!this.splitGraphs.getNewIDPProblems().isEmpty()) {
                    sb.append(eu.linebreak());
                    sb.append("It also ");
                }
            }

            if (!this.splitGraphs.getNewIDPProblems().isEmpty()) {
                sb.append("introduced ");
                sb.append(this.splitGraphs.getNewIDPProblems().size());
                if (this.splitGraphs.getNewIDPProblems().size() > 1) {
                    sb.append(" new IDPProblems.");
                } else {
                    sb.append(" new IDPProblem.");
                }
            }

        }

        private void exportStrictAndBound(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The following edge conditions have been oriented strictly: ");
            sb.append(eu.linebreak());
            this.exportEdgesToConditions(this.splitResult.strictEdges, sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            sb.append("The following edge conditions are bound: ");
            sb.append(eu.linebreak());
            this.exportEdgesToConditions(this.splitResult.boundEdges, sb, eu, verbosityLevel);
            sb.append(eu.linebreak());
        }

        private void exportEdgesToConditions(final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> edges, final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append(eu.tableStart(2));
            for (final Map.Entry<IEdge, ImmutableCollection<ItpfConjClause>> edgeEntry : edges.entrySet()) {
                final ArrayList<String> cols = new ArrayList<String>(2);
                cols.add(edgeEntry.getKey().export(eu, verbosityLevel));

                final StringBuilder clauseBuilder = new StringBuilder();
                final Iterator<ItpfConjClause> clauseIter = edgeEntry.getValue().iterator();
                while (clauseIter.hasNext()) {
                    clauseIter.next().export(clauseBuilder, eu, verbosityLevel);
                    if (clauseIter.hasNext()) {
                        clauseBuilder.append(eu.newline());
                    }

                }
                cols.add(clauseBuilder.toString());

                sb.append(eu.tableRow(cols));
            }
            sb.append(eu.tableEnd());

        }

        private void exportConstraintSummary(final Map<Itpf, Integer> finalConstraintToId,
            final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The following constraints had to be solved:");
            sb.append(eu.linebreak());
            sb.append(eu.linebreak());

            for (final Map.Entry<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> implication : this.splitResult.simplifiedImplications.entrySet()) {
                sb.append("The ");
                if (implication.getValue().size() > 1) {
                    sb.append("edges ");
                } else {
                    sb.append("edge ");
                }

                final Iterator<IEdge> edgesIterator =
                    implication.getValue().iterator();
                while (edgesIterator.hasNext()) {
                    edgesIterator.next().export(sb, eu, VerbosityLevel.MIDDLE);
                    if (edgesIterator.hasNext()) {
                        sb.append(", ");
                    }
                }

                sb.append(" gave rise to the following ");

                final Set<Itpf> constraints =
                    implication.getKey().getLastFormulaStates();

                if (constraints.size() != 1) {
                    sb.append("constaints:");
                } else {
                    sb.append("constaint:");
                }

                sb.append(eu.linebreak());

                for (final Itpf constraint : constraints) {
                    final Integer constraintId =
                        finalConstraintToId.get(constraint);

                    if (constraintId != null) {
                        sb.append("(");
                        sb.append(constraintId);
                        sb.append("): ");
                    }
                    constraint.export(sb, eu, verbosityLevel);
                    sb.append(eu.linebreak());
                }
            }
        }

        private void exportSideConstraintSummary(final Map<Itpf, Integer> finalConstraintToId,
            final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The following side constraints had to be solved:");
            sb.append(eu.linebreak());
            sb.append(eu.linebreak());

            for (final Map.Entry<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> varProof : this.splitResult.sideConstraints.y.entrySet()) {
                for (final Itpf constraint : varProof.getValue().getLastFormulaStates()) {
                    final Integer constraintId =
                        finalConstraintToId.get(constraint);

                    if (constraintId != null) {
                        sb.append("(");
                        sb.append(constraintId);
                        sb.append("): ");
                    }
                    constraint.export(sb, eu, verbosityLevel);
                    sb.append(eu.linebreak());
                }
            }
        }

        private Map<Itpf, Integer> exportImplicationProofs(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The constrains were derived the following way: ");
            sb.append(eu.linebreak());

            int nextEquiationId = 0;

            final Map<Itpf, Integer> allFinalEquations =
                new LinkedHashMap<Itpf, Integer>();

            for (final Map.Entry<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> implication : this.splitResult.simplifiedImplications.entrySet()) {
                sb.append("The ");
                if (implication.getValue().size() > 1) {
                    sb.append("edges ");
                } else {
                    sb.append("edge ");
                }

                final Iterator<IEdge> edgesIterator =
                    implication.getValue().iterator();
                while (edgesIterator.hasNext()) {
                    edgesIterator.next().export(sb, eu, VerbosityLevel.MIDDLE);
                    if (edgesIterator.hasNext()) {
                        sb.append(", ");
                    }
                }

                sb.append(" gave rise to the following derivation:");

                sb.append(eu.linebreak());

                final Pair<Integer, Map<Itpf, Integer>> finalEquations =
                    implication.getKey().export(sb, eu, verbosityLevel,
                        nextEquiationId);
                nextEquiationId = finalEquations.x;
                allFinalEquations.putAll(finalEquations.y);
            }

            return allFinalEquations;
        }

        private Map<Itpf, Integer> exportSideConstraintProofs(final StringBuilder sb,
            final Map<Itpf, Integer> finalEquationsToId, final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The side constrains were derived the following way: ");
            sb.append(eu.linebreak());

            int nextEquiationId = 0;

            final Map<Itpf, Integer> allFinalEquations =
                new LinkedHashMap<Itpf, Integer>();

            for (final Map.Entry<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> varProof : this.splitResult.sideConstraints.y.entrySet()) {
                sb.append("The variable ");
                varProof.getKey().export(sb, eu, verbosityLevel);
                sb.append(" with side constraint ");
                varProof.getValue().getStartFormula().export(sb, eu, verbosityLevel);
                sb.append(" gave rise to the following derivation:");

                sb.append(eu.linebreak());

                final Pair<Integer, Map<Itpf, Integer>> finalEquations =
                    varProof.getValue().export(sb, eu, verbosityLevel,
                        nextEquiationId);
                nextEquiationId = finalEquations.x;
                allFinalEquations.putAll(finalEquations.y);
                sb.append(eu.linebreak());
                sb.append(eu.linebreak());
            }

            return allFinalEquations;
        }
    }

    private static class SplitResult {

        public final PolyInterpretation<BigInt> solvingInterpretation;
        public final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> strictEdges;
        public final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> boundEdges;
        public final ImmutableMap<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications;
        public final ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> sideConstraints;

        public SplitResult(
                final PolyInterpretation<BigInt> solvingInterpretation,
                final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> strict,
                final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> bound,
                final ImmutableMap<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications, final ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> sideConstraints) {
            this.solvingInterpretation = solvingInterpretation;
            this.strictEdges = strict;
            this.boundEdges = bound;
            this.simplifiedImplications = simplifiedImplications;
            this.sideConstraints = sideConstraints;
        }

    }
}
