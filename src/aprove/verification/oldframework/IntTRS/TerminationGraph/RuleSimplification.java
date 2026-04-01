package aprove.verification.oldframework.IntTRS.TerminationGraph;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.PolynomialConstraint.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Transforms rules like f(x,y) -> f(x-1-1, y+y+y+y) | x +17 + 17 >= 0 & y - 17
 * -q7 <= 0 y+y > 0 into f(x,y) -> f(x-5, 4y) | x + 34 >= 0 & y - 34 <= 0
 * @author Matthias Hoelzel
 */
public class RuleSimplification {
    /**
     * Some rule. It is precious!
     */
    private final IGeneralizedRule preciousRule;

    /**
     * Stores the result!
     */
    private IGeneralizedRule resultRule;

    /**
     * Generates new names.
     */
    private final FreshNameGenerator ng;

    /**
     * Some aborter.
     */
    private final Abortion aborter;

    /**
     * Creates your new rule simplification!
     * @param rule some input rule
     * @param gen some name generator
     * @param abortion some aborter
     */
    public RuleSimplification(final IGeneralizedRule rule, final FreshNameGenerator gen, final Abortion abortion) {
        this.preciousRule = rule;
        this.ng = gen;
        this.aborter = abortion;
    }

    /**
     * Simplifies a whole set of rules.
     * @param rules a collection of rules
     * @param ng some name generator
     * @param aborter some aborter
     * @return a bunch of rules
     * @throws AbortionException can be aborted
     */
    public static LinkedHashSet<IGeneralizedRule> simplifyRules(
        final Collection<IGeneralizedRule> rules,
        final FreshNameGenerator ng,
        final Abortion aborter) throws AbortionException
    {
        if (rules == null || ng == null || aborter == null) {
            assert false : "Null parameter!";
            return null;
        }
        final LinkedHashSet<IGeneralizedRule> result = new LinkedHashSet<>(rules.size());

        for (final IGeneralizedRule rule : rules) {
            aborter.checkAbortion();
            final RuleSimplification ruleSimplification = new RuleSimplification(rule, ng, aborter);
            final IGeneralizedRule resultRule = ruleSimplification.simplify();
            if (!resultRule.getCondTerm().equals(ToolBox.buildFalse())) {
                result.add(resultRule);
            }
        }

        return result;
    }

    /**
     * Runs the simplifications.
     * @return the result rule
     * @throws AbortionException can be aborted
     */
    public IGeneralizedRule simplify() throws AbortionException {
        if (this.resultRule != null) {
            return this.resultRule;
        }

        this.runSimplification();

        return this.resultRule;
    }

    /**
     * Calculates the result!
     * @throws AbortionException can be aborted
     */
    private void runSimplification() throws AbortionException {
        // 1. Simplify the terms:
        final TRSFunctionApplication newLeftSide = (TRSFunctionApplication) this.simplifyTerm(this.preciousRule.getLeft());
        final TRSFunctionApplication newRightSide = (TRSFunctionApplication) this.simplifyTerm(this.preciousRule.getRight());
        this.aborter.checkAbortion();

        // 2. Simplify the condition:
        final Pair<TRSTerm, TRSSubstitution> r = this.simplifyCondition(this.preciousRule.getCondTerm());
        final TRSTerm newCondition = r.x;
        final TRSSubstitution varEqs = r.y;
        this.aborter.checkAbortion();

        // 3. Store result:
        this.resultRule = IGeneralizedRule.create(newLeftSide, newRightSide.applySubstitution(varEqs), newCondition);
    }

    /**
     * Simplifies a given term.
     * @param t some input term
     * @return a simplified term
     * @throws AbortionException can be aborted
     */
    private TRSTerm simplifyTerm(final TRSTerm t) throws AbortionException {
        return RuleSimplification.simplifyTerm(t, this.ng, this.aborter);
    }

    /**
     * Simplifies a given term.
     * @param t some input term
     * @param ng a name generator
     * @param aborter some aborter
     * @return a simplified term
     * @throws AbortionException can be aborted
     */
    public static TRSTerm simplifyTerm(final TRSTerm t, final FreshNameGenerator ng, final Abortion aborter)
    throws AbortionException {
        aborter.checkAbortion();
        if (t.isVariable()) {
            return t;
        }
        assert (t instanceof TRSFunctionApplication);
        final TRSFunctionApplication func = (TRSFunctionApplication) t;
        final FunctionSymbol symbol = func.getRootSymbol();
        if (!ToolBox.PREDEFINED.isPredefined(symbol)) {
            final ImmutableList<TRSTerm> arguments = func.getArguments();
            final List<TRSTerm> newArguments = new ArrayList<>(arguments.size());
            for (final TRSTerm argument : arguments) {
                newArguments.add(RuleSimplification.simplifyTerm(argument, ng, aborter));
            }
            return TRSTerm.createFunctionApplication(symbol, newArguments);
        } else {
            final VarPolynomial poly = ToolBox.intTermToPolynomial(t, ng);
            return poly.toTerm(ToolBox.PREDEFINED);
        }
    }

    /**
     * Simplifies a given condition term.
     * @param t some condition term
     * @return a simplified term
     * @throws AbortionException can be aborted
     */
    private Pair<TRSTerm, TRSSubstitution> simplifyCondition(final TRSTerm t) throws AbortionException {
        return RuleSimplification.simplifyCondition(t, this.ng, this.aborter);
    }

    /**
     * Simplifies a given condition term.
     * @param t some condition term
     * @return a simplified term
     * @throws AbortionException can be aborted
     */
    public static Pair<TRSTerm, TRSSubstitution> simplifyCondition(
        final TRSTerm t,
        final FreshNameGenerator ng,
        final Abortion aborter) throws AbortionException
    {
        assert t != null && t instanceof TRSFunctionApplication : "Strange condition: " + t;

        final LinkedHashSet<PolynomialConstraint> constraints =
            new LinkedHashSet<>(ToolBox.boolTermToPolynomialConstraints((TRSFunctionApplication) t, ng, aborter));

        /* AW: This relies on my understanding of the implementation (not the declaration!) of
           boolTermToPolynomialConstraints. Somebody should probably look over that and check
           if it actually does what it is supposed to do, especially in the case that the condition
           is constant or a boolean connection of constants */
        if (constraints.isEmpty()) {
            return new Pair<>(ToolBox.buildTrue(), TRSSubstitution.EMPTY_SUBSTITUTION);
        }

        // Filter unneeded constraints:
        final LinkedHashSet<PolynomialConstraint> toRemove = new LinkedHashSet<>(constraints.size());
        final LinkedHashSet<PolynomialConstraint> simpleEqualities = new LinkedHashSet<>(constraints.size());
        TRSSubstitution subst = TRSSubstitution.EMPTY_SUBSTITUTION;
        for (final PolynomialConstraint p1 : constraints) {
            aborter.checkAbortion();
            if (p1.getPolynomial().equals(VarPolynomial.ZERO)) {
                toRemove.add(p1);
                continue;
            }

            if (p1.getType().equals(PolynomialConstraintType.PCT_EQ)) {
                final VarPolynomial equaledPolynomial = p1.getPolynomial();
                final Set<String> vars = equaledPolynomial.getVariables();
                if (vars.size() == 1
                    && equaledPolynomial.getDegree() == 1
                    && equaledPolynomial.getConstantPart().isZero())
                {
                    final String var = vars.iterator().next();
                    final PolynomialConstraint simpleEq =
                        new PolynomialConstraint(
                            VarPolynomial.createVariable(var),
                            PolynomialConstraintType.PCT_EQ,
                            p1.getNameGenerator());
                    simpleEqualities.add(simpleEq);
                    subst =
                        subst.compose(TRSSubstitution.create(
                            TRSTerm.createVariable(var),
                            IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS)));
                    toRemove.add(p1);
                    continue;
                }
            }

            if (toRemove.contains(p1)) {
                continue;
            }

            for (final PolynomialConstraint p2 : constraints) {
                aborter.checkAbortion();
                if (p1.equals(p2)) {
                    continue;
                }

                // If the constraints are trivially unsatisfiable, then we just return false:
                if (p1.contradicts(p2)) {
                    return new Pair<>(ToolBox.buildFalse(), TRSSubstitution.EMPTY_SUBSTITUTION);
                } else if (p1.isStrongerThan(p2)) {
                    toRemove.add(p2);
                }
            }
        }

        constraints.removeAll(toRemove);

        // Create result term:
        TRSTerm result = ToolBox.buildTrue();
        for (final PolynomialConstraint pc : constraints) {
            final TRSTerm pcCond = pc.toTerm();
            if (result == null) {
                result = pcCond;
            } else {
                result = ToolBox.buildAnd(result, pcCond);
            }
        }

        TRSTerm eqResult = null;
        for (final PolynomialConstraint pc : simpleEqualities) {
            final TRSTerm pcCond = pc.toTerm();
            if (eqResult == null) {
                eqResult = pcCond;
            } else {
                eqResult = ToolBox.buildAnd(eqResult, pcCond);
            }
        }

        //Now apply the substitution and add the equalities:
        if (result != null) {
            result = result.applySubstitution(subst);
            if (eqResult != null) {
                result = ToolBox.buildAnd(result, eqResult);
            }
        } else {
            result = eqResult;
        }

        return new Pair<>(result, subst);
    }
}
