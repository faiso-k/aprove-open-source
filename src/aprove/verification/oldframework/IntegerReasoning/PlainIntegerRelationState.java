package aprove.verification.oldframework.IntegerReasoning;

import java.io.*;
import java.util.*;

import org.json.*;

import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * An integer state storing integer relations.
 * @author cryingshadow
 * @version $Id$
 */
public class PlainIntegerRelationState implements IntegerState {

    /**
     * @param formula Some SMT formula.
     * @param rel Some integer relation.
     * @param solver Some SMT solver.
     * @return True if the specified SMT solver can prove that the specified relation is implied by the specified
     *         formula. False otherwise.
     */
    public static boolean checkRelationWithSMTSolver(
        SMTExpression<SBool> formula,
        IntegerRelation rel,
        SMTSolver solver
    ) {
        solver.addAssertion(formula);
        solver.addAssertion(Core.not(rel.toSMTExp()));
        boolean returnValue = false;
        try {
            returnValue = solver.checkSAT() == YNM.NO;
        } catch (Exception e) {
            /*
             * The checkSAT method may fail, for example due to nonlinear arithmetic in the set of relations. In this
             * case, we just fall to false in order to continue the inference.
             */
        } finally {
            try {
                solver.dispose();
            } catch (IOException exception) {
                // there's nothing we can do
            }
        }
        return returnValue;
    }

    /**
     * The logic for the SMT solver.
     */
    private final SMTLIBLogic logic;

    /**
     * The set of relations.
     */
    private final ImmutableSet<IntegerRelation> set;

    /**
     * Factory to build SMT solvers.
     */
    private final SMTSolverFactory smtFactory;

    /**
     * @param s The set of relations.
     * @param factory Factory to build SMT solvers.
     * @param l The logic for the SMT solver.
     */
    public PlainIntegerRelationState(ImmutableSet<IntegerRelation> s, SMTSolverFactory factory, SMTLIBLogic l) {
        this.set = s;
        this.smtFactory = factory;
        this.logic = l;
    }

    /**
     * Creates an empty integer state.
     * @param factory Factory to build SMT solvers.
     * @param l The logic for the SMT solver.
     */
    public PlainIntegerRelationState(SMTSolverFactory factory, SMTLIBLogic l) {
        this(ImmutableCreator.create(Collections.emptySet()), factory, l);
    }

    @Override
    public IntegerState addRelation(IntegerRelation relation, Abortion aborter) {
        IntegerRelationSet newSet = this.toRelationSet();
        newSet.add(relation);
        return new PlainIntegerRelationState(ImmutableCreator.create(newSet), this.smtFactory, this.logic);
    }

    @Override
    public IntegerState addRelationSet(Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        IntegerRelationSet newSet = this.toRelationSet();
        for (IntegerRelation rel : relations) {
            newSet.add(rel);
        }
        return new PlainIntegerRelationState(ImmutableCreator.create(newSet), this.smtFactory, this.logic);
    }

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(IntegerRelation relation, Abortion aborter) {
        return
            new Pair<Boolean, PlainIntegerRelationState>(
                PlainIntegerRelationState.checkRelationWithSMTSolver(
                    this.toRelationSet().toSMTExp(),
                    relation,
                    this.smtFactory.getSMTSolver(this.logic, aborter)
                ),
                this
            );
    }

    @Override
    public String toDOTString() {
        final LLVMRelationComparator comp =
            new LLVMRelationComparator(new LLVMVariableComparator(new LLVMNameComparator()));
        StringBuilder res = new StringBuilder();
        IntegerRelationSet relSet = this.toRelationSet();
        res.append("Equations:\\n");
        res.append(DOTFormatter.toDOT(relSet.getEquations(), 5, comp));
        res.append("\\nUndirected Inequations:\\n");
        res.append(DOTFormatter.toDOT(relSet.getUndirectedInequalities(), 5, comp));
        res.append("\\nWeak Directed Inequations:\\n");
        res.append(DOTFormatter.toDOT(relSet.getWeakDirectedInequalities(), 5, comp));
        res.append("\\nStrict Directed Inequations:\\n");
        res.append(DOTFormatter.toDOT(relSet.getStrictDirectedInequalities(), 5, comp));
        return res.toString();
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", "PlainIntegerRelationState");
        res.put("relations", JSONExportUtil.toJSON(this.set));
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        return new IntegerRelationSet(this.set);
    }

    @Override
    public String toString() {
        return this.toRelationSet().toString();
    }

}
