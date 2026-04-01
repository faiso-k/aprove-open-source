package aprove.verification.oldframework.IntTRS.Ranking;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.PolynomialConstraint.*;
import aprove.verification.oldframework.Utility.*;

import static java.util.stream.Collectors.*;

/**
 * Rewrites rules to transition relations.
 * @author Matthias Hoelzel
 */
public class RuleToTransitionRelation {
    /**
     * Generates some new names.
     */
    private final FreshNameGenerator ng;

    /**
     * Some aborter
     */
    private final Abortion aborter;

    /**
     * Constructor! It creates your new iRule-to-Relation-Rewriter!
     * @param gen some name generator (should not be null)
     */
    public RuleToTransitionRelation(final FreshNameGenerator gen, final Abortion abortion) {
        this.ng = gen;
        this.aborter = abortion;
    }

    public TransitionRelation ruleToTransitionRelation(
            final IGeneralizedRule iRule,
            final boolean eliminateVariables) {
        return ruleToTransitionRelation(iRule, eliminateVariables, false);
    }

    /**
     * Rewrite an IGeneralizedRule to a transition relation.
     * @param iRule the input rule
     * @param eliminateVariables true, iff variables should be eliminated
     * @return your new transition relation
     * @throws AbortionException can aborted
     */
    public TransitionRelation ruleToTransitionRelation(
            final IGeneralizedRule iRule,
            final boolean eliminateVariables,
            final boolean linearOnly)
        throws AbortionException
    {
        TRSTerm condition = iRule.getCondTerm();
        if (condition == null) {
            condition = ToolBox.buildTrue();
        }
        final TRSFunctionApplication left = iRule.getLeft();
        final TRSFunctionApplication right = ((TRSFunctionApplication) iRule.getRight());

        final ArrayList<TRSVariable> rightVariables = new ArrayList<>(right.getRootSymbol().getArity());

        for (int i = 0; i < right.getRootSymbol().getArity(); i++) {
            final TRSVariable newVariable =
                TRSTerm.createVariable(this.ng.getFreshName(RankingUtil.RIGHT_VARIABLE_NAME, false));
            rightVariables.add(newVariable);
            final TRSTerm t = right.getArgument(i);
            condition = ToolBox.buildAnd(condition, ToolBox.buildEq(t, newVariable));
        }

        final LinkedList<TRSVariable> leftVariables = new LinkedList<>();
        for (final TRSTerm arg : left.getArguments()) {
            assert arg instanceof TRSVariable : "Left term should only have variables as arguments.";
            leftVariables.add((TRSVariable) arg);
        }

        List<PolynomialConstraint> polyConstraints =
            ToolBox.boolTermToPolynomialConstraints((TRSFunctionApplication) condition, this.ng, this.aborter);

        if (linearOnly) {
            polyConstraints = polyConstraints.stream().filter(x -> x.getPolynomial().isLinear()).collect(toList());
        }

        final List<GEConstraint> constraints = new LinkedList<>();

        for (final PolynomialConstraint pc : polyConstraints) {
            this.polynomialConstraintToGEConstraint(pc, constraints);
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("reduction");
            l.logln("Obtained the following polynomial constraints:");
            l.logln(polyConstraints);
            l.logln("Conversion into GEConstraints:");
            l.logln(constraints);
        }

        final PCS pcs = new PCS(constraints, this.aborter);

        final TransitionRelation newTR =
            new TransitionRelation(
                pcs,
                left.getRootSymbol(),
                leftVariables,
                right.getRootSymbol(),
                rightVariables,
                eliminateVariables,
                this.aborter);
        return newTR;
    }

    /**
     * Rewrites polynomial constraints to GEConstraints.
     * @param pc polynomial constraint
     * @param constraints list to fill in result constraints
     */
    private
        void
        polynomialConstraintToGEConstraint(final PolynomialConstraint pc, final List<GEConstraint> constraints)
    {
        final VarPolynomial vp = pc.getPolynomial();

        switch (pc.getType()) {
        case PCT_EQ:
            // t == 0 is equivalent to t >= 0 && t <= 0
            this.polynomialConstraintToGEConstraint(new PolynomialConstraint(
                vp,
                PolynomialConstraintType.PCT_GE,
                this.ng), constraints);
            this.polynomialConstraintToGEConstraint(new PolynomialConstraint(
                vp,
                PolynomialConstraintType.PCT_LE,
                this.ng), constraints);
            break;
        case PCT_GE:
            assert vp.isConcrete() : "Constraints should be concrete!";
            final BigInteger c = vp.getConstantPart().getNumericalAddend().negate();
            final VarPolynomial rest = vp.plus(VarPolynomial.create(c));

            final GEConstraint constraint = GEConstraint.create(rest, c);

            constraints.add(constraint);

            break;

        case PCT_LE:
            // t >= 0 is equivalent to -t <= 0
            this.polynomialConstraintToGEConstraint(new PolynomialConstraint(
                vp.negate(),
                PolynomialConstraintType.PCT_GE,
                this.ng), constraints);
            break;
        default:
            // The types PCT_LT, PCT_GT can not occur since we used the method
            // ToolBox.boolTermToPolynomialConstraints to generate the
            // constraints.
            assert false : "Default?!? Should not occur!";
        }
    }
}
