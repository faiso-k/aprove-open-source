package aprove.verification.complexity.CIdtProblem.Processors;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.CIdtProblem.Utility.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.idpframework.Processors.NonInf.Solving.*;
import aprove.verification.idpframework.Processors.NonInf.Solving.ItpfPolyConstraintsSolver.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 * copies a lot from MPluecker
 */
public class CIdtPolyIntRedPairProcessor extends CIdtProcessor<Result> {

    private final int RANGE_MIN;
    private final int RANGE_MAX;
    private final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> strategy;
    private final SolverType solverType;
    private final boolean all_Strict_And_Bounded;

    @ParamsViaArgumentObject
    public CIdtPolyIntRedPairProcessor(final Arguments arguments) {
        super("CIdtPolIntRedPairProcessor");
        if (Globals.useAssertions) {
            assert (arguments.RANGE_MIN <= arguments.RANGE_MAX);
        }
        this.strategy = arguments.obtainStrategy();
        this.solverType = arguments.solver;
        this.all_Strict_And_Bounded = arguments.all_Strict_And_Bounded;
        this.RANGE_MIN = arguments.RANGE_MIN;
        this.RANGE_MAX = arguments.RANGE_MAX;
    }

    @Override
    public boolean isCIdtApplicable(final CIdtProblem idt) {
        return idt.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    protected Result processCIdtProblem(final CIdtProblem idt,
        final Abortion aborter) throws AbortionException {

        final List<CIdtPolyIntRedPairGraphProof> graphProof =
            new ArrayList<CIdtPolyIntRedPairGraphProof>();

        final Set<CIdtProblem> newCIdtProblems = new LinkedHashSet<CIdtProblem>();

        boolean success = false;

        final PolyIntRedPairResult result = this.createResult(idt, aborter);
        Set<IEdge> newS = new LinkedHashSet<IEdge>(idt.getS());
        Set<IEdge> newK = new LinkedHashSet<IEdge>(idt.getK());

        if (result != null) {
            Set<IEdge> strictAndBoundIntersection =  this.getStrictAndBoundIntersection(result.strictEdges, result.boundEdges);
            newS.removeAll(strictAndBoundIntersection);
            newK.addAll(strictAndBoundIntersection);

            graphProof.add(new CIdtPolyIntRedPairGraphProof(result));
            success = true;
        }


        if (success) {
            CIdtProblem newCIdt = idt.change(idt.getIdpGraph(), ImmutableCreator.create(newS), ImmutableCreator.create(newK));
            newCIdtProblems.add(newCIdt);

            int degree = idt.getPolyInterpretation().getMaxDegree(idt.getIdpGraph().getDefinedSymbols());

            ComplexityValue upperBound = ComplexityValue.fixedDegreePoly(Math.abs(degree));

            final CIdtPolyIntRedPairProof proof =
                new CIdtPolyIntRedPairProof(ImmutableCreator.create(graphProof));

            return ResultFactory.provedMax(newCIdtProblems,
                UpperBound.create(new SumComputation(upperBound)), proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private Set<IEdge> getStrictAndBoundIntersection(final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> strictEdges,
        final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> boundEdges) {

        Set<IEdge> intersection = new LinkedHashSet<IEdge>();
        for (final Map.Entry<IEdge, ImmutableCollection<ItpfConjClause>> strictEntry : strictEdges.entrySet()) {
            final ImmutableCollection<ItpfConjClause> boundClauses =
                boundEdges.get(strictEntry.getKey());
            if (boundClauses != null) {
                intersection.add(strictEntry.getKey());

            }
        }

        return intersection;
    }

    private PolyIntRedPairResult createResult(final CIdtProblem idt,
        final Abortion aborter) throws AbortionException {

        final CIdtPolyIntRedPairImplicationGraph implicationGraph =
            new CIdtPolyIntRedPairImplicationGraph(idt);
        final CollectionMap<Itpf, IEdge> implications =
            implicationGraph.getImplications();

        final Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications =
            this.processEdgeImplications(idt, implicationGraph, implications,
                aborter);

        final Conjunction<Itpf> constraints =
            this.createConstraints(idt, simplifiedImplications, aborter);

        final ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> sideConstraints =
            this.createSideConstraints(idt, constraints, aborter);

        final LinkedHashSet<Itpf> totalConstraints = new LinkedHashSet<Itpf>(constraints.asCollection());
        totalConstraints.addAll(sideConstraints.x.asCollection());

        PolyInterpretation<BigInt> solution = null;
        aborter.checkAbortion();
        try {
            solution = this.solveConstraints(idt, new Conjunction<Itpf>(ImmutableCreator.create(totalConstraints)), aborter);
        } catch (final Exception e) {
            e.printStackTrace();
        }

        if (solution != null) {
            final Pair<ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>, ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>> strictAndBound =
                this.getStrictAndBoundedEdges(idt, implicationGraph, solution);

            return new PolyIntRedPairResult(solution, strictAndBound.x,
                strictAndBound.y, ImmutableCreator.create(simplifiedImplications), sideConstraints);
        } else {
            if (Globals.DEBUG_MARCEL) {
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

    private Conjunction<Itpf> createConstraints(final CIdtProblem idp,
        final Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications,
        final Abortion aborter) {
        final Set<Itpf> simplifiedConstraints = new LinkedHashSet<Itpf>();

        for (final ItpfSchedulerProof<Itpf, GenericItpfRule<?>> proof : simplifiedImplications.keySet()) {
            simplifiedConstraints.addAll(proof.getLastFormulaStates());
        }

        return new Conjunction<Itpf>(
            ImmutableCreator.create(simplifiedConstraints));
    }

    @SuppressWarnings("unchecked")
    private ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> createSideConstraints(final CIdtProblem idp,
        final Conjunction<Itpf> simplifiedConstraints,
        final Abortion aborter) throws AbortionException {

        final Set<Itpf> simplifiedSideConstraints = new LinkedHashSet<Itpf>();

        // add side constraints
        if (this.all_Strict_And_Bounded) {
            simplifiedSideConstraints.add(this.getStrictAndBoundedConstraint(idp, idp.getS(),
                ConstantType.StrictOrientation));
            simplifiedSideConstraints.add(this.getStrictAndBoundedConstraint(idp, idp.getS(),
                ConstantType.BoundOrientation));
        } else {
            Itpf strictandBoundedItpf = idp.getItpfFactory().createFalse();
            for (IEdge edge : idp.getS()) {
                Itpf strictItpf = this.getStrictAndBoundedConstraint(idp, edge,
                                    ConstantType.StrictOrientation);
                Itpf boundItpf = this.getStrictAndBoundedConstraint(idp, edge,
                    ConstantType.BoundOrientation);

                Itpf conj  =  idp.getItpfFactory().createAnd(strictItpf, boundItpf);
                strictandBoundedItpf = idp.getItpfFactory().createOr(strictandBoundedItpf, conj);
            }
            simplifiedSideConstraints.add(strictandBoundedItpf);
        }



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

    @SuppressWarnings("unchecked")
    private Itpf getStrictAndBoundedConstraint(final CIdtProblem idt,
        final ImmutableSet<IEdge> edges,
        final ConstantType constantType) {
        final PolyInterpretation<?> interpretation =
            idt.getIdpGraph().getPolyInterpretation();

        final ItpfFactory itpfFactory = idt.getItpfFactory();
        final IDependencyGraph graph = idt.getIdpGraph();
        Set<ItpfAtom> atoms = new LinkedHashSet<ItpfAtom>();

        Itpf itpf = itpfFactory.createTrue();
        for (final IEdge edge : edges) {

            itpf = itpfFactory.createAnd(this.getStrictAndBoundedConstraint(idt, edge, constantType));

            for (final ItpfConjClause conditionClause : graph.getCondition(edge)) {
                final ItpfBoolPolyVar<?> var =
                    interpretation.getItpfBooleanPolyVar(constantType, edge, conditionClause,
                        Collections.<Itpf> emptySet());
                atoms.add(var);
            }
        }

        return itpf;
    }

    private Itpf getStrictAndBoundedConstraint(final CIdtProblem idt, final IEdge edge, final ConstantType constantType) {
        final PolyInterpretation<?> interpretation = idt.getIdpGraph().getPolyInterpretation();

        final ItpfFactory itpfFactory = idt.getItpfFactory();
        ItpfConjClause strictAndBoundClause = itpfFactory.createEmptyClause();
        final IDependencyGraph graph = idt.getIdpGraph();
        Set<ItpfAtom> atoms = new LinkedHashSet<ItpfAtom>();

        for (final ItpfConjClause conditionClause : graph.getCondition(edge)) {
            final ItpfBoolPolyVar<?> var =
                interpretation.getItpfBooleanPolyVar(constantType, edge, conditionClause, Collections.<Itpf> emptySet());
            atoms.add(var);
        }

        strictAndBoundClause = itpfFactory.createClause(atoms, true, ITerm.EMPTY_SET);
        return itpfFactory.create(strictAndBoundClause);
    }

    private Pair<ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>, ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>>> getStrictAndBoundedEdges(final IDPProblem idp,
        final CIdtPolyIntRedPairImplicationGraph implicationGraph,
        final PolyInterpretation<BigInt> solution) {
        final CollectionMap<IEdge, ItpfConjClause> strictOrientation = new CollectionMap<IEdge, ItpfConjClause>();
        final CollectionMap<IEdge, ItpfConjClause> boundOrientation = new CollectionMap<IEdge, ItpfConjClause>();

        final IDependencyGraph graph = idp.getIdpGraph();
        for (final IEdge edge : implicationGraph.getEdges()) {
            if (edge.type.isInf()) {
                boolean allStrict = true;
                boolean allBounded = true;
                for (final ItpfConjClause conditionClause : graph.getCondition(edge)) {

                    final BigInt strictValue =
                        solution.getBooleanPolyVarValue(ConstantType.StrictOrientation, edge, conditionClause,
                            Collections.<Itpf> emptySet());
                    if (strictValue != null && strictValue.isOne()) {
                        strictOrientation.add(edge, conditionClause);
                    } else {
                        allStrict = false;
                    }
                    final BigInt boundValue =
                        solution.getBooleanPolyVarValue(ConstantType.BoundOrientation, edge, conditionClause,
                            Collections.<Itpf> emptySet());

                    if (boundValue != null && boundValue.isOne()) {
                        boundOrientation.add(edge, conditionClause);
                    } else {
                        allBounded = false;
                    }
                }
                if (!allStrict) {
                    strictOrientation.remove(edge);
                }
                if (!allBounded) {
                    boundOrientation.remove(edge);
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

        final SemiRingDomain<BigInt> VAR_RANGE = DomainFactory.createVarRange(BigInt.ZERO, BigInt.create(BigInteger.valueOf(this.RANGE_MIN)), BigInt.create(BigInteger.valueOf(this.RANGE_MAX)));

        final ItpfPolyConstraintsSolver solver =
            this.solverType.getSolver();
        aborter.checkAbortion();
        try {
            final PolyInterpretation<BigInt> solution;
            if (solver instanceof ItpfPolyDiophantineSatSolver) {
                solution =
                    ((ItpfPolyDiophantineSatSolver) solver).solve(idp.getPredefinedMap(),
                        (PolyInterpretation<BigInt>) idp.getIdpGraph().getPolyInterpretation(), constraints, VAR_RANGE,
                        aborter);
            } else {
                solution =
                    solver.solve(idp.getPredefinedMap(),
                        (PolyInterpretation<BigInt>) idp.getIdpGraph().getPolyInterpretation(), constraints, aborter);

            }
            return solution;

        } catch (final Exception e) {
            e.printStackTrace();
            return null;
        }
    }

    private Map<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> processEdgeImplications(final IDPProblem idp,
        final CIdtPolyIntRedPairImplicationGraph implicationGraph,
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

        public int RANGE_MAX = 3;
        public int RANGE_MIN = -3;

        public IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> obtainStrategy() {
            return CNDStrategy.CND_DefaultStrategy.getStrategy();
        }

        public SolverType solver = SolverType.SAT_SOLVER;

        public boolean all_Strict_And_Bounded = true;

    }

    public class CIdtPolyIntRedPairProof extends DefaultProof {

        private final ImmutableList<CIdtPolyIntRedPairGraphProof> subProofs;

        public CIdtPolyIntRedPairProof(
                final ImmutableList<CIdtPolyIntRedPairGraphProof> subProofs) {
            this.subProofs = subProofs;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();

            final Iterator<CIdtPolyIntRedPairGraphProof > subProofIterator =
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

    public static class CIdtPolyIntRedPairGraphProof extends IDPExportable.IDPExportableSkeleton {

        private final PolyIntRedPairResult result;

        public CIdtPolyIntRedPairGraphProof(final PolyIntRedPairResult result) {
            this.result = result;
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {

            sb.append(eu.linebreak());

            this.exportStrictAndBound(sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            sb.append("The following polynomial interpretation has been used:");
            sb.append(eu.linebreak());
            this.result.solvingInterpretation.export(sb, eu, verbosityLevel);
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

        private void exportStrictAndBound(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append("The following edge conditions have been oriented strictly: ");
            sb.append(eu.linebreak());
            this.exportEdgesToConditions(this.result.strictEdges, sb, eu, verbosityLevel);
            sb.append(eu.linebreak());

            sb.append("The following edge conditions are bound: ");
            sb.append(eu.linebreak());
            this.exportEdgesToConditions(this.result.boundEdges, sb, eu, verbosityLevel);
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

            for (final Map.Entry<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> implication : this.result.simplifiedImplications.entrySet()) {
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
                    sb.append("constraints:");
                } else {
                    sb.append("constraint:");
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

            for (final Map.Entry<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> varProof : this.result.sideConstraints.y.entrySet()) {
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

            for (final Map.Entry<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> implication : this.result.simplifiedImplications.entrySet()) {
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
            sb.append("The side constraints were derived the following way: ");
            sb.append(eu.linebreak());

            int nextEquiationId = 0;

            final Map<Itpf, Integer> allFinalEquations =
                new LinkedHashMap<Itpf, Integer>();

            for (final Map.Entry<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> varProof : this.result.sideConstraints.y.entrySet()) {
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

    private static class PolyIntRedPairResult {

        public final PolyInterpretation<BigInt> solvingInterpretation;
        public final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> strictEdges;
        public final ImmutableMap<IEdge, ImmutableCollection<ItpfConjClause>> boundEdges;
        public final ImmutableMap<ItpfSchedulerProof<Itpf, GenericItpfRule<?>>, ImmutableSet<IEdge>> simplifiedImplications;
        public final ImmutablePair<Conjunction<Itpf>, ImmutableMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>> sideConstraints;

        public PolyIntRedPairResult(
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
