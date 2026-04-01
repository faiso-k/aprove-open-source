package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Unwinding.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Attempts to prove termination of a ProgramGraph using safety
 * @author marinag
 */
public final class Cooperation {

    /**
     * Cooperation process result
     */
    private CooperationResult result = null;

    /**
     * The cooperation graph, includes a safety and termination copies of the original graph
     */
    private CooperationGraph coopGraph;

    private final Abortion aborter;

    private Unwinding unwind;

    private final IRSwTProblem intTRS;

    /**
     * @param intTRS
     * @param aborter
     * @return
     */
    public static Cooperation create(final IRSwTProblem intTRS, final Abortion aborter) {
        return new Cooperation(intTRS, aborter);
    }

    /**
     * @param intTRS
     * @param abortion
     */
    public Cooperation(final IRSwTProblem intTRS, final Abortion aborter) {
        this.intTRS = intTRS;
        this.aborter = aborter;
    }

    /**
     * @param aborter
     * @return result of the cooperation process
     */
    public CooperationResult getResult(final boolean partial) {
        if (this.result == null) {
            this.coopGraph = CooperationGraph.create(this.intTRS, this.aborter);
            this.result = this.refinement();
        }
        return this.result;
    }

    /**
     * Tries refining the ranking function at cut point
     * @param rf
     * @param errorPath
     * @return true is was successful, false otherwise
     */
    private boolean tryRefine(final ErrorPath errorPath) {
        final LinLexRanking rf = this.coopGraph.getCurrentCutPoint().getRanking();
        final LinearTransitionPair tp = errorPath.getTransitionPair();
        final boolean insertResult = rf.insert(errorPath.getStemBounded(), tp);
        if (insertResult) {
            this.refine();
        }
        return insertResult;
    }

    /**
     * Tries to refine the ranking function in the context of the error path
     * @param rf
     * @param errorPath
     * @param unwind
     * @return true is was successful, false otherwise
     */
    private boolean tryRefineScc(final ErrorPath errorPath) {
        final LinLexRanking rf = this.coopGraph.getCurrentCutPoint().getRanking();
        final Set<Edge<LinearTransitionPairsSet, LocationID>> context =
            this.coopGraph.getTermSccContext(errorPath.getCycleNodes());
        final List<Edge<LinearTransitionPair, LocationID>> toKeep = new ArrayList<>();
        for (Edge<LinearTransitionPairsSet, LocationID> edge : context) {
            if (
                !((CoopLocation) edge.getEndNode()).getType().equals(CoopLocationType.CUTPOINT_DUPLICATE)
                && !((CoopLocation) edge.getEndNode()).getType().equals(CoopLocationType.ERROR)
            ) {
                toKeep.addAll(LinearProgramGraph.splitEdge(edge));
            }
        }
        Log.report("Cycle", errorPath.getTransitionPair().toString());
        for (final Edge<LinearTransitionPair, LocationID> item : toKeep) {
            Log.report("context", item.getStartNode().getObject().toString()
                + item.getEndNode().getObject().toString()
                + item.getObject().y.trim().toString());
        }
        final Pair<Boolean, List<Edge<LinearTransitionPair, LocationID>>> resultP =
            rf.findOrientingRankingInsert(
                errorPath.getTransitionPair(),
                errorPath.getStemBounded(),
                errorPath.getCycle(),
                toKeep
            );
        final List<Edge<LinearTransitionPair, LocationID>> result = resultP.y;
        final List<Edge<LinearTransitionPair, LocationID>> toRemove = new ArrayList<>();
        Log.report("tryRefineScc", "Result: " + (!result.isEmpty() ? rf : "Fail"));
        if (result.isEmpty()) {
            return false;
        } else {
            for (Edge<LinearTransitionPair, LocationID> se : result) {
                final Edge<LinearTransitionPairsSet, LocationID> p =
                    this.coopGraph.getEdge(se.getStartNode(), se.getEndNode());
                this.removeEdge(se);
                toRemove.add(se);
            }
            for (Edge<LinearTransitionPair, LocationID> spe : toKeep) {
                if (!errorPath.getCycle().contains(new Edge<>(spe.getStartNode(), spe.getEndNode()))) {
                    continue;
                }
                if (rf.isBoundedAndDecreasing(spe.getObject())) {
                    this.removeEdge(spe);
                    toRemove.add(spe);
                }
            }
            this.refine();
        }
        return true;
    }

    /**
     * @param e
     * @return remove edge from the termination part
     */
    private boolean removeEdge(final Edge<LinearTransitionPair, LocationID> e) {
        final Edge<LinearTransitionPairsSet, LocationID> p = this.coopGraph.getEdge(e.getStartNode(), e.getEndNode());
        if (p == null) {
            return true;
        }
        final LinearTransitionPairsSet newCond = p.getObject().remove(e.getObject());
        if (newCond.getTransitionsPairs().isEmpty()) {
            this.coopGraph.removeEdge(p);
            Log.report("removeEdge", p.toString());
        } else {
            Log.report("removeEdge - partial", e.toString());
            this.coopGraph.replaceEdge(
                p.getStartNode(),
                p.getEndNode(),
                newCond);
        }
        return true;
    }

    /**
     * Attempts to refines the cooperation graph and returns the appropriate result
     * @param partial
     * @param aborter
     * @return corresponding result
     */
    private CooperationResult refinement() {
        this.aborter.checkAbortion();
        UnwindingResult unwindResult = null;
        while (this.coopGraph.hasNextCutPoint()) {
            if (this.coopGraph.openCurrentCutPoint()) {
                this.unwind = new Unwinding(this.coopGraph, this.aborter);
                while (
                    !this.coopGraph.currentCutPointUnreachable()
                    && (unwindResult = this.unwind.getResult()) instanceof Unwinding.Unsafe
                ) {
                    this.aborter.checkAbortion();
                    final Unwinding.Unsafe uResult = (Unwinding.Unsafe) unwindResult;
                    final ErrorPath errorPath = new ErrorPath(this.coopGraph, uResult.getErrorPath());
                    for (final Edge<LinearTransitionPair, LocationID> e : uResult.getErrorPath()) {
                        Log.report("errPath", e.toString());
                    }
                    Log.report("EP", errorPath.getTransitionPair().toString());
                    Log.report("EP-stem", errorPath.getStem().toString());
                    Log.report("EP-cycle", errorPath.getCycle().toString());
                    if (this.tryRefineScc(errorPath)) {
                        this.unwind = new Unwinding(this.coopGraph, this.aborter);
                        //                        if (this.coopGraph.currentCutPointUnreachable()) {
                        //                            break;
                        //                        }
                    } else if (!this.tryRefine(errorPath)) {
                        this.coopGraph.closeCurrentCutPoint();
                        final Pair<IRSwTProblem, Set<IGeneralizedRule>> remaining = this.coopGraph.getRemaining();
                        final Map<TRSFunctionApplication, List<SimplePolynomial>> ranking = this.coopGraph.getRanking();
                        if (this.isNonTerminatingLin(errorPath)) {
                            return new CooperationNonTerminating(errorPath);
                        } else {
                            return new CooperationUnknown(ranking, remaining.x, remaining.y);
                        }
                    }
                    Log.report("RF", this.coopGraph.getCurrentCutPoint().getRanking().toString());
                }
                this.coopGraph.closeCurrentCutPoint();
            }
        }
        final IRSwTProblem remaining = new IRSwTProblem(ImmutableCreator.create(new HashSet<IGeneralizedRule>()));
        final Map<TRSFunctionApplication, List<SimplePolynomial>> ranking = this.coopGraph.getRanking();
        Log.report("FM", this.coopGraph.getVarsToFApp().toString());
        return new CooperationTerminating(ranking);
    }

    /**
     * Updates the error condition of a given cut point with the refined functions tree
     * @param unwind
     * @param toRemove
     */
    private void refine() {
        this.coopGraph.refineCurrentCutPoint();
        this.unwind = new Unwinding(this.coopGraph, this.aborter);
    }

    private boolean isNonTerminatingLin(final ErrorPath errorPath) {
        if (!this.coopGraph.getSubstitution().isEmpty()) {
            return false;
        }
        final LinearTransitionPair cycle = errorPath.getTransitionPair();
        final LinearTransitionPair post = new LinearTransitionPair(cycle.x, cycle.y);
        final LinearTransitionPair stem = errorPath.getStemTransitionPair();
        final LinearConstraintsSystem A = stem.x;
        final LinearConstraintsSystem B = stem.y.apply(cycle.x);
        final LinearConstraintsSystem C = A.merge(B);
        final ConstraintsSystemSolver solver = ConstraintsSystemSolver.create(this.aborter);
        if (!solver.isSAT(C)) {
            return false;
        }
        final Set<SimplePolyConstraint> constraints = new HashSet<>();
        for (final SimplePolyConstraint c : A.toSet()) {
            if (
                stem.y.compare(c.getPolynomial(), ConstraintType.GE)
                && cycle.y.compare(c.getPolynomial(), ConstraintType.GE)
            ) {
                constraints.add(c);
            }
        }
        final LinearConstraintsSystem uA = LinearConstraintsSystem.create(constraints);
        final LinearConstraintsSystem L = cycle.x;
        final LinearConstraintsSystem pL = cycle.compose(cycle).x;
        final Set<String> existVars = new HashSet<>();
        existVars.addAll(pL.getVariables());
        existVars.removeAll(cycle.y.getVariablesNames());
        existVars.removeAll(L.getVariables());
        final Z3ExtSolverFactory solverFactory = new Z3ExtSolverFactory();
        final SMTSolver smtSolver = solverFactory.getSMTSolver(SMTLIBLogic.AUFLIA, this.aborter);
        final VariableScope scope = new VariableScope();
        final SMTExpression<SBool> z = uA.toSMTExp(scope);
        final SMTExpression<SBool> x = L.toSMTExp(scope);
        SMTExpression<SBool> y = pL.toSMTExp(scope);
        final SBool s = SBool.representative;
//        final List<Symbol0<? extends Sort>> uniSyms = new ArrayList<>();
        final List<Symbol0<? extends Sort>> existSyms = new ArrayList<>();
        for (final String v : existVars) {
            existSyms.add(scope.intVar(v));
        }
        Log.report("stem", uA.toString());
        Log.report("cond", L.toString());
        Log.report("post", pL.toString());
        Log.report("exist", existVars.toString());
        if (!existSyms.isEmpty()) {
            y = Core.exists(s, existSyms, y);
        }
        smtSolver.addAssertion(z);
        smtSolver.addAssertion(x);
        smtSolver.addAssertion(Core.not(y));
        final YNM res = smtSolver.checkSAT();
        return res.equals(YNM.NO);
    }

    /**
     * @return the current cooperation graph
     */
    public CooperationGraph getCooperationGraph() {
        return this.coopGraph;
    }

}
