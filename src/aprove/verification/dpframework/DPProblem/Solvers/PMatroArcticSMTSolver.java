package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.PMATRO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A solver for arctic matrix interpretations using SMT.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PMatroArcticSMTSolver implements QActiveSolver {

    /**
     * The SMT solving engine.
     */
    protected final SMTEngine engine;

    /**
     * The dimension of the matrices.
     */
    protected final int dimension;

    /**
     * Whether to use integers or natural numbers in the ArcticInts.
     */
    protected final boolean belowZero;

    private final String[] yicesCommands = {
        "(define-type arctic (tuple bool int))",
        "(define zero::arctic)",
        "(assert (= zero (mk-tuple true 0)))",
        "(define one::arctic)",
        "(assert (= one (mk-tuple false 0)))",
        // "(define finite::(-> arctic bool))",
        // "(define agt::(-> arctic arctic bool))",
        // "(define aeq::(-> arctic arctic bool))",
        // "(define age::(-> arctic arctic bool))",
        // "(define max::(-> int int int))",
        // "(define aplus::(-> arctic arctic arctic))",
        // "(define atimes::(-> arctic arctic arctic))",
    };

    private final List<String> yicesFramework = Arrays.asList(this.yicesCommands);

    protected PMatroArcticSMTSolver(
            final SMTEngine engine,
            final int dimension,
            final boolean belowZero) {
        this.engine = engine;
        this.dimension = dimension;
        this.belowZero = belowZero;
    }

    public static PMatroArcticSMTSolver create(
            final SMTEngine engine,
            final int dimension,
            final boolean belowZero) {
        return new PMatroArcticSMTSolver(engine, dimension, belowZero);
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter)
            throws AbortionException {
        if (Globals.DEBUG_ULRICHSG) {
            System.out.println("BelowZero is " + this.belowZero + ", allstrict is " + allstrict);
        }

        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(P, OrderRelation.GR);

        // create a new interpretation and interpret all function symbols
        // occurring in the pConstraints
        ArcticMatrixSMTInterpretation interpretation =
            ArcticMatrixSMTInterpretation.create(
                    pConstraints, this.dimension, this.belowZero, allstrict);

        // generate constraints
        String usableRulesConstraint = interpretation.getActiveRuleConstraints(R, aborter);
        String newConstraint = interpretation.fromTermConstraints(pConstraints, aborter);
        if (Globals.DEBUG_ULRICHSG) {
            System.out.println(interpretation);
            // System.out.println("DP constraint is " + newConstraint);
            // System.out.println("UsableRuleConstraint is " + usableRulesConstraint);
        }
        StringBuilder sb = new StringBuilder();
        for (String command : this.yicesFramework) {
            sb.append(command);
            sb.append("\n");
        }
        sb.append(interpretation.getVariableDeclarations());
        for (String assertion : interpretation.getAssertions()) {
            sb.append(assertion);
        }
        sb.append("(assert ");
        sb.append(newConstraint);
        sb.append(")\n");
        if (usableRulesConstraint != null) {
            sb.append("(assert ");
            sb.append(usableRulesConstraint);
            sb.append(")\n");
        }
        sb.append("(assert ");
        sb.append(interpretation.getFinitenessConstraint());
        sb.append(")\n");
        if (!this.belowZero) {
            sb.append("(assert ");
            sb.append(interpretation.getAboveZeroConstraint());
            sb.append(")\n");
        }
        sb.append("(check)\n");

        final String yicesInput = sb.toString();

        // Call the SMT checker
        Pair<YNM, Map<String, String>> resPair;
        try {
            resPair = this.engine.solve(yicesInput, SMTLogic.QF_LIA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Yices error: " + e.getErrorMessage());
            resPair = new Pair<>(YNM.MAYBE, null);
        }
        final Map<String, String> resMap = resPair.y;
        if (resPair.x != YNM.YES || resMap == null) {
            // SMT checker returned UNSAT or something unknown
            return null;
        }

        if (Globals.DEBUG_ULRICHSG) {
            System.out.println("From yices: " + resMap);
        }

        Map<GPolyVar, ArcticInt> substitution =
            new HashMap<GPolyVar, ArcticInt>();
        for (Map.Entry<String, String> entry : resMap.entrySet()) {
            substitution.put(GAtomicVar.createVariable(entry.getKey()),
                    ArcticInt.fromYices(entry.getValue()));
        }

        interpretation = interpretation.specialize(substitution, ArcticInt.ZERO, aborter);

        FullSharingFactory<ArcticInt, GPolyVar> matrixPolyFactory =
            new FullSharingFactory<ArcticInt, GPolyVar>();
        FullSharingFactory<GPoly<ArcticInt, GPolyVar>, GPolyVar>matrixBigPolyFactory =
            new FullSharingFactory<GPoly<ArcticInt, GPolyVar>, GPolyVar>();
        OrderPolyFactory<ArcticInt> matrixOrderPolyFactory =
            new OrderPolyFactory<ArcticInt>(matrixBigPolyFactory, matrixPolyFactory);

        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        GPolyFlatRing<GPoly<ArcticInt, GPolyVar>, GPolyVar> outerFlatRing =
            new SimpleGPolyFlatRing<GPoly<ArcticInt, GPolyVar>, GPolyVar>(
                    matrixPolyFactory, monoid);
        FlatteningVisitor<GPoly<ArcticInt, GPolyVar>, GPolyVar> fv =
            new FlatteningVisitor<GPoly<ArcticInt, GPolyVar>, GPolyVar>(outerFlatRing);

        GPolyFlatRing<ArcticInt, GPolyVar> innerFlatRing =
            new SimpleGPolyFlatRing<ArcticInt, GPolyVar>(ArcticSemiring.create(), monoid);
        FlatteningVisitor<ArcticInt, GPolyVar> fvInner =
            new FlatteningVisitor<ArcticInt, GPolyVar>(innerFlatRing);
        //PMATROExoticInt<ArcticInt> solvingOrder = new PMATROExoticInt<ArcticInt>(
        //        interpretation, matrixOrderPolyFactory, fvInner, fv, ArcticIntOrder.create());
        // return solvingOrder;
        return null;
    }
}
