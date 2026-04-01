package aprove.verification.oldframework.IntegerReasoning.smt;

import java.io.*;
import java.util.*;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.skeletons.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * Hands over queries over integer relations to an underlying SMT solver. The
 * solver can be chosen by passing the desired SMTSolverFactory at creation.
 * @author Alexander Weinert
 */
public class SmtIntegerState extends SkeletonIntegerState {

    /**
     * The currently asserted relations
     */
    private final IntegerRelationSet relations;

    /**
     * A factory that produces SMTSolvers. Used to get a fresh SMT solver for each query.
     */
    private final SMTSolverFactory solverFactory;

    /**
     * Creates a new SmtIntegerState without any asserted relations
     * @param solverFactory Some SMTSolverFactory
     */
    public SmtIntegerState(final SMTSolverFactory solverFactory) {
        this.solverFactory = solverFactory;
        this.relations = new IntegerRelationSet();
    }

    /**
     * Creates a new SmtIntegerState with the given internal variables. Only
     * used for deep copying. Does not copy the parameters, but just keeps the
     * references.
     *
     * @param solverFactory Some SMTSolverFactory
     * @param relations Some relationset
     */
    private SmtIntegerState(final SMTSolverFactory solverFactory, final IntegerRelationSet relations) {
        this.solverFactory = solverFactory;
        this.relations = relations;
    }

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(final IntegerRelation relation, Abortion aborter) {
        final SMTExpression<SBool> knowledgeBase = this.relations.toSMTExp();
        final SMTExpression<SBool> relationAsExpression = relation.toSMTExp();
        if (this.checkImplication(knowledgeBase, relationAsExpression)) {
            return new Pair<Boolean, IntegerState>(true, this);
        }
        return new Pair<Boolean, IntegerState>(false, this);
    }

    @Override
    public String toDOTString() {
        return "SMTIntegerInterface: " + this.relations.toString();
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("solver_factory", JSONExportUtil.toJSON(this.solverFactory));
        res.put("relations", JSONExportUtil.toJSON(this.relations));
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        return new IntegerRelationSet(this.relations);
    }

    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder("{");
        final Iterator<IntegerRelation> it = this.relations.iterator();
        while(it.hasNext()) {
            builder.append(it.next());
            if(it.hasNext()) {
                builder.append(", ");
            }
        }
        builder.append("}");
        //return builder.toString();
        return "";
    }

    @Override
    protected void addRelationMutate(final IntegerRelation relation) {
        this.relations.add(relation);
    }

    @Override
    protected SkeletonIntegerState deepCopy() {
        final IntegerRelationSet relationSetCopy = new IntegerRelationSet(this.relations);
        return new SmtIntegerState(this.solverFactory, relationSetCopy);
    }

    @Override
    protected IntegerState merge(final IntegerState other) {
        assert other instanceof SmtIntegerState;
        final IntegerRelationSet mergedRelationSet = new IntegerRelationSet();
        mergedRelationSet.addAll(this.relations);
        mergedRelationSet.addAll(((SmtIntegerState) other).relations);
        return new SmtIntegerState(this.solverFactory, mergedRelationSet);
    }

    @Override
    protected void renameMutate(final Map<IntegerVariable, IntegerVariable> renaming) {
        this.relations.applySubstitution(renaming);
    }

    private boolean checkImplication(
        final SMTExpression<SBool> knowledgeBase,
        final SMTExpression<SBool> implicationCandidate
    ) {
        final SMTSolver solver = this.solverFactory.getSMTSolver(SMTLIBLogic.QF_LIA, AbortionFactory.create(), false);
        solver.addAssertion(knowledgeBase);
        solver.addAssertion(Core.not(implicationCandidate));
        boolean returnValue;
        try {
            final YNM solverResult = solver.checkSAT();
            returnValue = (solverResult == YNM.NO);
        } catch (Exception e) {
            /* checkSAT may fail, for example due to nonlinear arithmetic in the set of relations.
             * In this case, we just fall to false in order to continue the inference */
            returnValue = false;
        }
        this.disposeSolverOrSilenceError(solver);
        return returnValue;
    }

    /**
     * Tries to free resources taken by the solver. Silences any errors this
     * might yield.
     */
    private void disposeSolverOrSilenceError(final SMTSolver solver) {
        try {
            solver.dispose();
        } catch (final IOException exception) {
            // There's nothing we can do
        }
    }

}
