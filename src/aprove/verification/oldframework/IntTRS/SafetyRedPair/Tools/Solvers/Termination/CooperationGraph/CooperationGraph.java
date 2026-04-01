package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author marinag
 *
 */
public class CooperationGraph extends LinearProgramGraph {
    /**
     *
     */
    private static final long serialVersionUID = -6317859136408403846L;

    private final Stack<CutPointDupLocation> cutPoints;
    private final Map<Edge<LinearTransitionPairsSet, LocationID>, Edge<LinearTransitionPairsSet, LocationID>> stash;
    private final LinearTransitionPairsSet snapshotTransition;
    private final LinearTransitionPairsSet initTransition;
    private final DisjunctionSolver solver;
    private final PolyRelation errorRelation;
    private final ProblemGraph originalProblem;
    private final Map<Location, FunctionSymbol> locToFSym;
    private final ProgramGraph pg;

    /*
     * Found lexicographic ranking of closed cut points
     */
    private final Map<TRSFunctionApplication, List<SimplePolynomial>> ranking = new HashMap<>();

    /**
     * @param edges
     * @param cutPoints
     * @param variables
     * @param locToFSym
     * @param solver
     */
    private CooperationGraph(
        final ProgramGraph pg,
        final Stack<CutPointDupLocation> cutPoints,
        final Set<String> variables,
        final ProblemGraph originalProblem,
        final Map<Location, FunctionSymbol> locToFSym,
        final DisjunctionSolver solver)
    {
        super(pg);
        this.cutPoints = cutPoints;
        this.stash = new HashMap<>();
        this.snapshotTransition = CooperationGraph.createSnapshotTransition(variables);
        this.errorRelation = CooperationGraph.createErrorRelation(variables);
        this.initTransition = CooperationGraph.createInitTransition(variables);
        this.solver = solver;
        this.originalProblem = originalProblem;
        this.locToFSym = locToFSym;
        this.pg = pg;
    }

    /**
     *
     */
    public CooperationGraph() {
        super();
        this.cutPoints = new Stack<>();
        this.stash = new HashMap<>();
        this.snapshotTransition = null;
        this.errorRelation = null;
        this.initTransition = null;
        this.solver = null;
        this.originalProblem = null;
        this.locToFSym = null;
        this.pg = null;
    }

    /**
     * @param pD cut point duplicate
     * @return true if cut point was indeed activated, false otherwise
     */
    private boolean openCutPoint(final CutPointDupLocation pD) {
        if (Globals.useAssertions) {
            assert this.stash.isEmpty();
        }
        this.stash.clear();
        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());

        if (!this.contains(pT)) {
            return false;
        }
        final HashSet<Edge<LinearTransitionPairsSet, LocationID>> outEdges = new HashSet<>();
        for (final Edge<LinearTransitionPairsSet, LocationID> edge : this.getOutEdges(pT)) {
            if (this.hasPath(edge.getEndNode(), edge.getStartNode())) {
                outEdges.add(edge);
            }
        }
        if (outEdges.isEmpty()) {
            // cut point unreachable, nothing to do here
            return false;
        }
        final Edge<LinearTransitionPairsSet, LocationID> safetyEdge =
            new Edge<>(LocationCreator.safetyCopy(pD.getOriginalLocation()), pD, this.snapshotTransition); //LinearTransitionPairsSet.create());
            this.addEdge(safetyEdge);

            for (final Edge<LinearTransitionPairsSet, LocationID> t : outEdges) {
                final Edge<LinearTransitionPairsSet, LocationID> newT = new Edge<>(pD, t.getEndNode(), t.getObject());
                this.addEdge(newT);
                this.removeEdge(t);
                this.stash.put(t, newT);
            }
            this.refineCurrentCutPoint();

            return true;
    }

    //    /**
    //     * @param pD cut point duplicate
    //     * @return true if cut point was indeed activated, false otherwise
    //     */
    //    private boolean openCutPoint__(final CutPointDupLocation pD) {
    //        if (Globals.useAssertions) {
    //            assert this.stash.isEmpty();
    //        }
    //        this.stash.clear();
    //        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());
    //
    //        if (!this.contains(pT)) {
    //            return false;
    //        }
    //        final HashSet<Edge<LinearTransitionPairsSet, LocationID>> outEdges = new HashSet<>();
    //        for (final Edge<LinearTransitionPairsSet, LocationID> edge : this.getOutEdges(pT)) {
    //            if (this.hasPath(edge.getEndNode(), edge.getStartNode())) {
    //                outEdges.add(edge);
    //            }
    //        }
    //        if (outEdges.isEmpty()) {
    //            // cut point unreachable, nothing to do here
    //            return false;
    //        }
    //        final Edge<LinearTransitionPairsSet, LocationID> safetyEdge =
    //            new Edge<>(LocationCreator.safetyCopy(pD.getOriginalLocation()), pT, this.initTransition); //LinearTransitionPairsSet.create());
    //            this.addEdge(safetyEdge);
    //
    //            for (final Edge<LinearTransitionPairsSet, LocationID> t : outEdges) {
    //                final Edge<LinearTransitionPairsSet, LocationID> newT = new Edge<>(pD, t.getEndNode(), t.getObject());
    //                this.addEdge(newT);
    //                this.removeEdge(t);
    //                this.stash.put(t, newT);
    //            }
    //            final Edge<LinearTransitionPairsSet, LocationID> nspEdge = new Edge<>(pT, pD, this.snapshotTransition);
    //            this.addEdge(nspEdge);
    //            this.refineCurrentCutPoint();
    //
    //            Log.report("CG+cp", this.toTikZ());
    //
    //            return true;
    //    }
    //
    //    /**
    //     * @param pD cut point duplicate
    //     * @return true if cut point was indeed activated, false otherwise
    //     */
    //    private boolean openCutPoint_(final CutPointDupLocation pD) {
    //        //        if (Globals.useAssertions) {
    //        //            assert this.stash.isEmpty();
    //        //        }
    //        //        this.stash.clear();
    //        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());
    //
    //        if (!this.contains(pT)) {
    //            return false;
    //        }
    //        final HashSet<Edge<LinearTransitionPairsSet, LocationID>> outEdges = new HashSet<>();
    //        for (final Edge<LinearTransitionPairsSet, LocationID> edge : this.getOutEdges(pT)) {
    //            if (this.hasPath(edge.getEndNode(), edge.getStartNode())) {
    //                outEdges.add(edge);
    //            }
    //        }
    //        if (outEdges.isEmpty()) {
    //            // cut point unreachable, nothing to do here
    //            return false;
    //        }
    //        final Edge<LinearTransitionPairsSet, LocationID> safetyEdge =
    //            new Edge<>(LocationCreator.safetyCopy(pD.getOriginalLocation()), pT, this.initTransition);
    //            this.addEdge(safetyEdge);
    //
    //            for (final Edge<LinearTransitionPairsSet, LocationID> t : outEdges) {
    //                final Edge<LinearTransitionPairsSet, LocationID> newT = new Edge<>(pD, t.getEndNode(), t.getObject());
    //                this.addEdge(newT);
    //                this.removeEdge(t);
    //                this.stash.put(t, newT);
    //            }
    //
    //            final Edge<LinearTransitionPairsSet, LocationID> nspEdge = new Edge<>(pT, pD, this.snapshotTransition);
    //            this.addEdge(nspEdge);
    //            this.refineCurrentCutPoint();
    //
    //            // Log.report("CG+cp", this.toTikZ());
    //
    //            return true;
    //    }
    //
    //
    //    /**
    //     * close current cut point duplicate (remove it's edges and error location)
    //     */
    //    public void closeCurrentCutPoint_() {
    //        if (Globals.useAssertions) {
    //            assert !this.cutPoints.isEmpty();
    //        }
    //
    //
    //        //
    //        //        for (final Entry<Edge<LinearTransitionPairsSet, LocationID>, Edge<LinearTransitionPairsSet, LocationID>> pair : this.stash
    //        //            .entrySet())
    //        //        {
    //        //            final Edge<LinearTransitionPairsSet, LocationID> newT =
    //        //                this.getEdge(pair.getValue().getStartNode(), pair.getValue().getEndNode());
    //        //            if (newT == null) {
    //        //                continue;
    //        //            }
    //        //            this.removeEdge(newT);
    //        //            final Edge<LinearTransitionPairsSet, LocationID> t = pair.getKey();
    //        //            final Edge<LinearTransitionPairsSet, LocationID> refinedT =
    //        //                new Edge<>(t.getStartNode(), t.getEndNode(), newT.getObject());
    //        //                this.addEdge(refinedT);
    //        //        }
    //        //
    //        //        this.stash.clear();
    //        final CutPointDupLocation pD = this.cutPoints.pop();
    //
    //        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());
    //        final Location pE = LocationCreator.abortLocation(pD.getOriginalLocation());
    //        final Location pS = LocationCreator.safetyCopy(pD.getOriginalLocation());
    //
    //        this.removeEdge(pT, pE);
    //        this.removeEdge(pS, pT);
    //        //        this.removeNode(pD);
    //
    //        final FunctionSymbol fSym = this.locToFSym.get(pD.getOriginalLocation());
    //        final ArrayList<Term> args = new ArrayList<>();
    //
    //        final Edge<LinearTransitionPairsSet, LocationID> edge = this.getOutEdges(pS).iterator().next();
    //        for (final Pair<String, SimplePolynomial> entry : edge.getObject().getTransitionsPairs().iterator().next().y
    //            .getTransitions())
    //        {
    //            args.add(Term.createVariable(entry.getKey()));
    //        }
    //
    //        if (fSym != null) {
    //            this.ranking.put(
    //                Term.createFunctionApplication(fSym, new ArrayList<>(args.subList(0, fSym.getArity()))),
    //                pD.getRanking().getPolynomials());
    //        }
    //    }

    /**
     * close current cut point duplicate (remove it's edges and error location)
     */
    public void closeCurrentCutPoint() {
        if (Globals.useAssertions) {
            assert !this.cutPoints.isEmpty();
        }

        for (final Entry<Edge<LinearTransitionPairsSet, LocationID>, Edge<LinearTransitionPairsSet, LocationID>> pair : this.stash
            .entrySet())
        {
            final Edge<LinearTransitionPairsSet, LocationID> newT =
                this.getEdge(pair.getValue().getStartNode(), pair.getValue().getEndNode());
            if (newT == null) {
                continue;
            }
            this.removeEdge(newT);
            final Edge<LinearTransitionPairsSet, LocationID> t = pair.getKey();
            final Edge<LinearTransitionPairsSet, LocationID> refinedT =
                new Edge<>(t.getStartNode(), t.getEndNode(), newT.getObject());
                this.addEdge(refinedT);
        }

        this.stash.clear();
        final CutPointDupLocation pD = this.cutPoints.pop();

        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());
        final Location pE = LocationCreator.abortLocation(pD.getOriginalLocation());
        final Location pS = LocationCreator.safetyCopy(pD.getOriginalLocation());

        this.removeEdge(pT, pE);
        this.removeEdge(pS, pD);
        this.removeNode(pD);

        final FunctionSymbol fSym = this.locToFSym.get(pD.getOriginalLocation());
        final ArrayList<TRSTerm> args = new ArrayList<>();

        final Edge<LinearTransitionPairsSet, LocationID> edge = this.getOutEdges(pS).iterator().next();
        for (final Pair<String, SimplePolynomial> entry : edge.getObject().getTransitionsPairs().iterator().next().y
            .getTransitions())
        {
            args.add(TRSTerm.createVariable(entry.getKey()));
        }

        if (fSym != null) {
            this.ranking.put(
                TRSTerm.createFunctionApplication(fSym, new ArrayList<>(args.subList(0, fSym.getArity()))),
                pD.getRanking().getPolynomials());
        }
    }

    //    /**
    //     * close current cut point duplicate (remove it's edges and error location)
    //     */
    //    public void closeCurrentCutPoint__() {
    //        if (Globals.useAssertions) {
    //            assert !this.cutPoints.isEmpty();
    //        }
    //
    //        for (final Entry<Edge<LinearTransitionPairsSet, LocationID>, Edge<LinearTransitionPairsSet, LocationID>> pair : this.stash
    //            .entrySet())
    //        {
    //            final Edge<LinearTransitionPairsSet, LocationID> newT =
    //                this.getEdge(pair.getValue().getStartNode(), pair.getValue().getEndNode());
    //            if (newT == null) {
    //                continue;
    //            }
    //            this.removeEdge(newT);
    //            final Edge<LinearTransitionPairsSet, LocationID> t = pair.getKey();
    //            final Edge<LinearTransitionPairsSet, LocationID> refinedT =
    //                new Edge<>(t.getStartNode(), t.getEndNode(), newT.getObject());
    //            this.addEdge(refinedT);
    //        }
    //
    //        this.stash.clear();
    //        final CutPointDupLocation pD = this.cutPoints.pop();
    //
    //        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());
    //        final Location pE = LocationCreator.abortLocation(pD.getOriginalLocation());
    //        final Location pS = LocationCreator.safetyCopy(pD.getOriginalLocation());
    //
    //        this.removeEdge(pT, pE);
    //        this.removeEdge(pS, pT);
    //        this.removeNode(pD);
    //
    //        final FunctionSymbol fSym = this.locToFSym.get(pD.getOriginalLocation());
    //        final ArrayList<Term> args = new ArrayList<>();
    //
    //        final Edge<LinearTransitionPairsSet, LocationID> edge = this.getOutEdges(pS).iterator().next();
    //        for (final Pair<String, SimplePolynomial> entry : edge.getObject().getTransitionsPairs().iterator().next().y
    //            .getTransitions())
    //        {
    //            args.add(Term.createVariable(entry.getKey()));
    //        }
    //
    //        if (fSym != null) {
    //            this.ranking.put(
    //                Term.createFunctionApplication(fSym, new ArrayList<>(args.subList(0, fSym.getArity()))),
    //                pD.getRanking().getPolynomials());
    //        }
    //    }


    /**
     * @return true if managed to activate ("open") a cut point, false otherwise (=no valid cut points left)
     */
    public boolean openCurrentCutPoint() {
        if (Globals.useAssertions) {
            assert !this.cutPoints.isEmpty() && this.stash.isEmpty();
        }

        while (!this.cutPoints.isEmpty()) {
            if (this.openCutPoint(this.cutPoints.peek())) {
                return true;
            } else {
                Log.report("Coop", "cutPoint u-r: " + this.cutPoints.peek());
                this.cutPoints.pop();
            }
        }
        return false;
    }

    /**
     * @return true if has no yet activated cut points, false otherwise (doesn't check if they are valid, aka reachable)
     */
    public boolean hasNextCutPoint() {
        return !this.cutPoints.isEmpty();
    }

    //    public ProgramGraph getTermSubGraph() {
    //        if (this.termSubGraph == null) {
    //            this.termSubGraph = new HashSet<>();
    //
    //            for (final Node<LocationID> l : this.getNodes()) {
    //                final Location loc = (Location) (l);
    //                if (((CoopLocation) loc).getType().isTermination()) {
    //                    this.termSubGraph.add(loc);
    //                }
    //            }
    //        }
    //
    //        return new ProgramGraph(this.getSubGraph(this.termSubGraph));
    //    }




    /**
     * @param nodes set of graph nodes
     * @return termination subgraph context of the given nodes (any node that has an either an in-coming or out-coming path to the nodes set)
     */
    public Set<Edge<LinearTransitionPairsSet, LocationID>> getTermSccContext(final Set<Node<LocationID>> nodes) {
        final Set<Edge<LinearTransitionPairsSet, LocationID>> inEdges =
            new HashSet<>(this.getSubGraph(nodes).getEdges());
            final Set<Edge<LinearTransitionPairsSet, LocationID>> outEdges =
                new HashSet<>(this.getSubGraph(nodes).getEdges());

                Set<Edge<LinearTransitionPairsSet, LocationID>> newInEdges = new HashSet<>(inEdges);
                Set<Edge<LinearTransitionPairsSet, LocationID>> newOutEdges = new HashSet<>(outEdges);

                while (!newInEdges.isEmpty()) {
                    inEdges.addAll(newInEdges);
                    final Set<Edge<LinearTransitionPairsSet, LocationID>> candidates = new HashSet<>();
                    for (final Edge<LinearTransitionPairsSet, LocationID> e : newInEdges) {
                        for (final Edge<LinearTransitionPairsSet, LocationID> c : this.getInEdges(e.getStartNode())) {
                            if (!((CoopLocation) c.getStartNode()).getType().isSafety()) {
                                candidates.add(c);
                            }
                        }
                    }
                    newInEdges = new HashSet<>();
                    candidates.removeAll(inEdges);
                    newInEdges.addAll(candidates);
                }

                while (!newOutEdges.isEmpty()) {
                    outEdges.addAll(newOutEdges);
                    final Set<Edge<LinearTransitionPairsSet, LocationID>> candidates = new HashSet<>();
                    for (final Edge<LinearTransitionPairsSet, LocationID> e : newOutEdges) {
                        for (final Edge<LinearTransitionPairsSet, LocationID> c : this.getOutEdges(e.getEndNode())) {
                            candidates.add(c);
                        }
                    }
                    newOutEdges = new HashSet<>();
                    candidates.removeAll(outEdges);
                    newOutEdges.addAll(candidates);
                }
                final Set<Edge<LinearTransitionPairsSet, LocationID>> edges = new HashSet<>(inEdges);
                edges.addAll(outEdges);
                return edges;
    }

    /**
     * @return true if current cut point is reachable from its duplicate, false otherwise
     */
    public boolean currentCutPointUnreachable() {
        final CutPointDupLocation cP = this.cutPoints.peek();
        final Location pT = LocationCreator.termCopy(cP.getOriginalLocation());

        if (!this.contains(cP) || !this.hasPath(cP, pT)) {
            return true;
        }

        return false;
    }

    /**
     * @param variables set of variables to create snapshots for
     * @return program transition of snapshots assignments
     */
    private static LinearTransitionPairsSet createSnapshotTransition(final Set<String> variables) {
        final List<Pair<String, SimplePolynomial>> map = new ArrayList<>();
        final List<String> varsAll = new ArrayList<>();

        map.add(new Pair<>(CooperationGraph.CP_VARIABLE, SimplePolynomial.ONE));
        varsAll.add(CooperationGraph.CP_VARIABLE);

        for (final String var : variables) {
            map.add(new Pair<>(var, SimplePolynomial.create(var)));
            map.add(new Pair<>(CooperationGraph.createSnapshot(var), SimplePolynomial.create(var)));
            varsAll.add(var);
        }
        final LinearConstraintsSystem condition =
            LinearConstraintsSystem.create(new SimplePolyConstraint(
                SimplePolynomial.create(CooperationGraph.CP_VARIABLE).negate(),
                ConstraintType.GE));

        final Set<LinearTransitionPair> pairs = new HashSet<>();
        pairs.add(new LinearTransitionPair(condition, PolyRelation.createRelation(map)));

        return LinearTransitionPairsSet.create(pairs);
    }

    /**
     * @param variables set of variables to create snapshots for
     * @return program transition of snapshots assignments
     */
    private static LinearTransitionPairsSet createInitTransition(final Set<String> variables) {
        final List<Pair<String, SimplePolynomial>> map = new ArrayList<>();
        final List<String> varsAll = new ArrayList<>();

        map.add(new Pair<>(CooperationGraph.CP_VARIABLE, SimplePolynomial.ZERO));
        varsAll.add(CooperationGraph.CP_VARIABLE);

        for (final String var : variables) {
            map.add(new Pair<>(var, SimplePolynomial.create(var)));
            map.add(new Pair<>(CooperationGraph.createSnapshot(var), SimplePolynomial.create(CooperationGraph.createSnapshot(var))));
            varsAll.add(var);
        }
        final LinearConstraintsSystem condition = LinearConstraintsSystem.LIN_TRUE;

        final Set<LinearTransitionPair> pairs = new HashSet<>();
        pairs.add(new LinearTransitionPair(condition, PolyRelation.createRelation(map)));

        return LinearTransitionPairsSet.create(pairs);
    }


    /**
     * @param variables program variables
     * @return relation to error transition (the variables are not changed)
     */
    private static PolyRelation createErrorRelation(final Set<String> variables) {
        final List<String> varsAll = new ArrayList<>();

        for (final String var : variables) {
            varsAll.add(var);
            varsAll.add(CooperationGraph.createSnapshot(var));
        }
        varsAll.add(CooperationGraph.CP_VARIABLE);

        return PolyRelation.createIdentity(varsAll);
    }

    /**
     *
     */
    private static String SNAPSHOT_POSTFIX = "^c";

    /**
     *
     */
    private static String CP_VARIABLE = "CP" + CooperationGraph.SNAPSHOT_POSTFIX;

    /**
     * @param variable program variable
     * @return snapshot variable for given variable
     */
    private static String createSnapshot(final String variable) {
        return variable + CooperationGraph.SNAPSHOT_POSTFIX;
    }

    /**
     * Initial error condition (snapshots assigned)
     */
    public static LinearConstraintsSystem ERROR_CONDITION = //ToolBox.buildGe(CP_VARIABLE, ToolBox.buildInt(BigInteger.ONE));
        LinearConstraintsSystem.create(new SimplePolyConstraint(
            SimplePolynomial.create(CooperationGraph.CP_VARIABLE),
            ConstraintType.GT));

    /**
     * @return the currently active cut point
     */
    public CutPointDupLocation getCurrentCutPoint() {
        assert !this.cutPoints.isEmpty();

        return this.cutPoints.peek();
    }

    /**
     * refine error condition of current cut point
     */
    public void refineCurrentCutPoint() {
        final CutPointDupLocation pD = this.cutPoints.peek();

        final Location pT = LocationCreator.termCopy(pD.getOriginalLocation());
        final Location eT = LocationCreator.abortLocation(pD.getOriginalLocation());

        final LinearDisjunction condition =
            LinearDisjunction.create(pD.getRanking().toErrorCondition()); //.addToAll(ERROR_CONDITION));
        // TermTools.buildAnd(ERROR_CONDITION.toTerm(), .toTerm());

        Log.report("errCond", condition.toString());
        this.replaceEdge(pT, eT, LinearTransitionPairsSet.create(
            condition,
            this.errorRelation));
    }


    /**
     * Assumptions: left term arguments are only variables, all function symbols have same arity
     * @param intTRS
     * @param aborter
     * @return
     */
    public static CooperationGraph create(final IRSwTProblem intTRS, final Abortion aborter) {

        // Create FunctionSymbol graph, with set of rules ass edges
        final FunctionSymbol startSym = intTRS.getStartTerm().getRootSymbol();
        ProblemGraph problemGraph = ProblemGraph.create(intTRS);

        final List<Node<FunctionSymbol>> cutPs = problemGraph.getCutPoints();

        // Create termination graph, consisting only of SCC of the problem graph
        final Set<Edge<Set<IGeneralizedRule>, FunctionSymbol>> termEdges = new HashSet<>();

        for (final ProblemGraph scc : problemGraph.getSCCProblems()) {
            for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : scc.getEdges()) {
                final Set<IGeneralizedRule> rules = new HashSet<>();
                rules.addAll(edge.getObject());
                termEdges.add(new Edge<>(edge.getStartNode(), edge.getEndNode(), rules));
            }
        }

        ProblemGraph terminationGraph = ProblemGraph.create(termEdges); //.compress(cutPs, aborter);

        final Set<TRSVariable> unchanged = new HashSet<>(); //problemGraph.getUnchangedVariables();

        // try remove reducing & bounded rules from the termination SCCs
        final Set<IGeneralizedRule> removed = terminationGraph.removeBoundedAndDecreasingRules(aborter, unchanged);

        for (final Node<FunctionSymbol> p : new HashSet<>(cutPs)) {
            boolean toKeep = false;
            if (terminationGraph.contains(p)) {
                for (final Node<FunctionSymbol> c : terminationGraph.getOut(p)) {
                    if (terminationGraph.hasPath(c, p)) {
                        toKeep = true;
                        break;
                    }
                }
            }
            if (!toKeep) {
                cutPs.remove(p);
            } else {
                Log.report("coop", "remining cut point: " + p);
            }
        }
        Log.report("coop", "remining cut points " + cutPs.size());

        if (cutPs.isEmpty()) {
            // no cut points left!
            return new CooperationGraph();
        }

        problemGraph = problemGraph.getNormalizedProblem();

        terminationGraph = terminationGraph.getNormalizedProblem();

        //Create now the graph
        final Map<Node<FunctionSymbol>, Location> nodeToLoc = new HashMap<>();

        int locId = 1;

        nodeToLoc.put(
            problemGraph.getStartNode(), new Location(locId++));

        for (final Node<FunctionSymbol> node : problemGraph.getNodes()) {
            nodeToLoc.put(node, new Location(locId++));
        }

        final DisjunctionSolver solver = DisjunctionSolver.create(ConstraintsSystemSolver.create(aborter), aborter);
        final FunctionSymbol startLoc = intTRS.getStartTerm().getRootSymbol();

        final HashMap<Node<FunctionSymbol>, Location> sMap = new HashMap<>();
        final HashMap<Node<FunctionSymbol>, Location> tMap = new HashMap<>();

        sMap.put(problemGraph.getStartNode(), LocationCreator.safetyCopy(
            nodeToLoc.get(problemGraph.getStartNode())));
        ProgramGraph coopGraph = new ProgramGraph(sMap.get(startLoc));

        final Set<TRSVariable> variables = new HashSet<>();

        // the safety copy
        for (final Node<FunctionSymbol> l : problemGraph.getNodes()) {
            if (!sMap.containsKey(l)) {
                sMap.put(l, LocationCreator.safetyCopy(nodeToLoc.get(l)));
            }
            final Location sLoc = sMap.get(l);
            for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> t : problemGraph.getOutEdges(l)) {
                final TermTransitionPairsSet trans = TermTransitionPairsSet.create(t.getObject());
                if (trans.getTransitionsPairs().isEmpty()) {
                    continue;
                }
                final Location d = nodeToLoc.get(t.getEndNode());
                if (!sMap.containsKey(t.getEndNode())) {
                    sMap.put(t.getEndNode(), LocationCreator.safetyCopy(d));
                }
                final Location sChild = sMap.get(t.getEndNode());
                coopGraph.addEdge(sLoc, sChild, trans);
            }
        }

        int varCount = 0;

        for (final Node<FunctionSymbol> fSym : nodeToLoc.keySet()) {
            if (fSym.getObject().getArity() > varCount) {
                varCount = fSym.getObject().getArity();
            }
        }

        for (int i = 0; i < varCount; i++) {
            variables.add(TRSTerm.createVariable("y" + i));
        }

        // the termination copy
        for (final Node<FunctionSymbol> l : terminationGraph.getNodes()) {
            if (!tMap.containsKey(l)) {
                final Location oLoc = nodeToLoc.get(l);
                tMap.put(l, LocationCreator.termCopy(oLoc));
            }
            final Location tLoc = tMap.get(l);
            for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> t : terminationGraph.getOutEdges(l)) {
                final TermTransitionPairsSet trans = TermTransitionPairsSet.create(t.getObject());

                if (trans.getTransitionsPairs().isEmpty()) {
                    continue;
                }

                final Location d = nodeToLoc.get(t.getEndNode());
                if (!tMap.containsKey(t.getEndNode())) {
                    final Location oLoc = d;
                    tMap.put(t.getEndNode(), LocationCreator.termCopy(oLoc));
                }
                final Location tChild = tMap.get(t.getEndNode());
                coopGraph.addEdge(tLoc, tChild, trans);
            }
        }

        // prepare cut point duplicates
        final Stack<CutPointDupLocation> cutPoints = new Stack<>();
        for (final Node<FunctionSymbol> l : cutPs) { // terminationGraph.getCutPoints()) {
            cutPoints.push(new CutPointDupLocation(nodeToLoc.get(l), CooperationGraph.SNAPSHOT_POSTFIX, aborter));
        }

        final Set<TRSVariable> usedVariables = new HashSet<>();
        usedVariables.addAll(usedVariables);

        for (final Edge<TermTransitionPairsSet, LocationID> edge : coopGraph.getEdges()) {
            usedVariables.addAll(edge.getObject().getVariables());
        }

        final Map<Location, FunctionSymbol> locToFSym = new HashMap<>();
        for (final Entry<Node<FunctionSymbol>, Location> entry : nodeToLoc.entrySet()) {
            locToFSym.put(entry.getValue(), entry.getKey().getObject());
        }

        coopGraph = new ProgramGraph(sMap.get(problemGraph.getStartNode()), coopGraph.getEdges());

        final Set<String> varNames = new HashSet<>();

        for (final TRSVariable v : variables) {
            varNames.add(v.getName());
        }

        return new CooperationGraph(
            coopGraph, cutPoints, varNames, problemGraph, locToFSym, solver);
    }


    /**
     * @return the safety subgraph of the cooperation graph, which also corresponds to the original problem graph
     */
    public LinearProgramGraph getOriginalGraph() {

        final Set<Node<LocationID>> safetyNodes = new HashSet<>();
        for (final Node<LocationID> node : this.getNodes()) {
            if (((CoopLocation) node).getType().isSafety()) {
                safetyNodes.add(node);
            }
        }

        return new LinearProgramGraph(
            this.getStartLocation(),
            this.getSubGraph(safetyNodes).getEdges(),
            this.getVarsToFApp(),
            this.getFSymToVars());
    }

    public LinearProgramGraph getTerminationGraph() {
        final Set<Node<LocationID>> termNodes = new HashSet<>();
        for (final Node<LocationID> node : this.getNodes()) {
            if (((CoopLocation) node).getType().isTermination()) {
                termNodes.add(node);
            }
        }
        return new LinearProgramGraph(
            null,
            this.getSubGraph(
                termNodes).getEdges(),
                this.getVarsToFApp(),
                this.getFSymToVars());
    }

    public ProblemGraph getOriginalProblem() {
        return this.createProblemGraph(this.getOriginalGraph());
    }

    public ProblemGraph getTerminationSubProblemGraph() {
        return this.createProblemGraph(this.getTerminationGraph());
    }

    public ProblemGraph createProblemGraph(final LinearProgramGraph pg) {
        final Map<Node<LocationID>, FunctionSymbol> locToFSymb = new HashMap<>();

        for (final Node<LocationID> node : pg.getNodes()) {
            if (node instanceof GraphCoopLocation) {
                final GraphCoopLocation coopLoc = (GraphCoopLocation) node;

                locToFSymb.put(node, this.locToFSym.get(coopLoc.getOriginalLocation()));
            }
        }

        final Set<IGeneralizedRule> rules = new HashSet<>();

        for (final Edge<LinearTransitionPairsSet, LocationID> edge : pg.getEdges()) {
            final FunctionSymbol lfSym = locToFSymb.get(edge.getStartNode());
            final FunctionSymbol rfSym = locToFSymb.get(edge.getEndNode());

            if (lfSym != null && rfSym != null) {
                rules.addAll(edge.getObject().createRules(lfSym, rfSym, pg.getSubstitution()));
            }
        }

        final FunctionSymbol fs = pg.getStartLocation() == null ? null : locToFSymb.get(pg.getStartLocation());
        return ProblemGraph.create(rules, fs);
    }

    public boolean isReduced() {
        return !this.getRemaining().y.isEmpty();
    }

    public Pair<IRSwTProblem, Set<IGeneralizedRule>> getRemaining() {
        final ProblemGraph pg = this.getOriginalProblem();
        final ProblemGraph tg = this.getTerminationSubProblemGraph();

        final Map<Pair<FunctionSymbol,FunctionSymbol>, Edge<Set<IGeneralizedRule>, FunctionSymbol>> tgEdges = new HashMap<>();

        for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : tg.getEdges()) {
            tgEdges.put(new Pair<>(edge.getStartNode().getObject(), edge.getEndNode().getObject()), edge);
        }

        int count;
        boolean reduced;

        final Set<IGeneralizedRule> dropped = new HashSet<>();

        do {
            count = pg.getAllRules().size();
            reduced = false;
            final LinkedHashSet<Cycle<FunctionSymbol>> SCCs = pg.getSCCs();
            final Map<Cycle<FunctionSymbol>, Node<Cycle<FunctionSymbol>>> sccToNode = new HashMap<>();

            for (final Cycle<FunctionSymbol> scc : SCCs) {
                sccToNode.put(scc, new Node<>(scc));
            }

            final SimpleGraph<Cycle<FunctionSymbol>, Boolean> sccDAG = new SimpleGraph<>();

            for (final Cycle<FunctionSymbol> sccA : SCCs) {
                for (final Cycle<FunctionSymbol> sccB : SCCs) {
                    if (pg.determineReachableNodes(sccA).containsAll(sccB)) {
                        sccDAG.addEdge(sccToNode.get(sccA), sccToNode.get(sccB), true);
                    } else if (pg.determineReachableNodes(sccB).containsAll(sccA)) {
                        sccDAG.addEdge(sccToNode.get(sccB), sccToNode.get(sccA), true);
                    }
                }
            }

            for (final Entry<Cycle<FunctionSymbol>, Node<Cycle<FunctionSymbol>>> entry : sccToNode.entrySet()) {
                if (sccDAG.determineReachableNodes(Arrays.asList(entry.getValue())).size() == 1) {
                    for (final Edge<Set<IGeneralizedRule>, FunctionSymbol> edge : pg
                        .getSubGraph(entry.getKey())
                        .getEdges())
                    {
                        pg.removeEdge(edge);

                        final Set<IGeneralizedRule> rules = new HashSet<>();
                        rules.addAll(edge.getObject());

                        final Pair<FunctionSymbol, FunctionSymbol> p =
                            new Pair<>(edge.getStartNode().getObject(), edge.getEndNode().getObject());

                            if (tgEdges.containsKey(p)) {
                                pg.addEdge(tgEdges.get(p));
                                rules.removeAll(tgEdges.get(p).getObject());
                            }

                            dropped.addAll(rules);
                    }
                }
            }

            final int currentCount = pg.getAllRules().size();
            reduced = count > currentCount;
            count = currentCount;
        } while (reduced);

        return new Pair<>(pg.toIntTRS(), dropped);
    }

    public IGeneralizedRule getRule(final Edge<LinearTransitionPair, LocationID> edge) {
        if ((edge.getStartNode() instanceof CoopLocation) && (edge.getEndNode() instanceof CoopLocation)) {
            final FunctionSymbol lfSym = this.locToFSym.get(((CoopLocation) edge.getStartNode()).getOriginalLocation());
            final FunctionSymbol rfSym = this.locToFSym.get(((CoopLocation) edge.getEndNode()).getOriginalLocation());

            return edge.getObject().createRule(lfSym, rfSym, this.getSubstitution());
        }
        return null;
    }

    public Set<IGeneralizedRule> getRules(final Edge<LinearTransitionPairsSet, LocationID> edge) {
        if ((edge.getStartNode() instanceof CoopLocation) && (edge.getEndNode() instanceof CoopLocation)) {
            final FunctionSymbol lfSym = this.locToFSym.get(((CoopLocation) edge.getStartNode()).getOriginalLocation());
            final FunctionSymbol rfSym = this.locToFSym.get(((CoopLocation) edge.getEndNode()).getOriginalLocation());

            return edge.getObject().createRules(lfSym, rfSym, this.getSubstitution());
        }
        return null;
    }

    public static CooperationGraph create() {
        return new CooperationGraph();
    }

    public Map<TRSFunctionApplication, List<SimplePolynomial>> getRanking() {
        return this.ranking;
    }

}
