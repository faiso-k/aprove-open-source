package aprove.verification.oldframework.IntTRS.TerminationGraph;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Chains two rules R1 and R2 together, simulating the effect of applying both
 * rules (first R1 then R2!).
 * @author Matthias Hoelzel
 */
public class Chaining {
    /**
     * Rule R1
     */
    private final IGeneralizedRule rule1;

    /**
     * Rule R2
     */
    private final IGeneralizedRule rule2;

    /**
     * Generates unused names.
     */
    private final FreshNameGenerator ng;

    /**
     * The result-rule.
     */
    private IGeneralizedRule output;

    /**
     * Constructor!
     * @param inputRule1 first rule
     * @param inputRule2 second rule
     * @param gen some name generator
     */
    public Chaining(final IGeneralizedRule inputRule1, final IGeneralizedRule inputRule2, final FreshNameGenerator gen) {
        this.rule1 = inputRule1;
        this.rule2 = inputRule2;
        this.ng = gen;
        this.output = null;
    }

    /**
     * Returns the result.
     * @return some rule
     */
    public IGeneralizedRule getResult() {
        if (this.output == null) {
            this.createOutput();
        }

        return this.output;
    }

    /**
     * After some renaming the result of the chaining will be calculated.
     */
    private void createOutput() {
        this.output =
            this.chaining(ToolBox.renameVariablesInRule(this.rule1, this.ng),
                ToolBox.renameVariablesInRule(this.rule2, this.ng));
    }

    /**
     * It merges rules of the form f(x_1, .. ,x_n) -> g(t_1, .. ,t_m) | phi1 and
     * g(y_1, .. ,y_m) -> h(s_1, .. ,s_k) | phi2 into one rule of the form
     * f(x_1, .. ,x_n) -> h(s_1 sigma, .. ,s_k sigma) | phi1 && (phi2 sigma),
     * where sigma(y_i) = t_i. Please note, that we assume that the rules are
     * variable-disjoint and that the rules are of the form as above.
     * @param firstRule the first rule
     * @param secondRule the second rule
     * @return rule that simulates the first and second rule
     */
    private IGeneralizedRule chaining(final IGeneralizedRule firstRule,
        final IGeneralizedRule secondRule) {
        final TRSSubstitution matcher =
            secondRule.getLeft().getMatcher(firstRule.getRight());

        if (matcher == null) {
            return null;
        }

        final TRSTerm newLeft = firstRule.getLeft();
        final TRSTerm newRight = secondRule.getRight().applySubstitution(matcher);
        final TRSTerm newCondition =
            ToolBox.buildAnd(firstRule.getCondTerm(),
                secondRule.getCondTerm().applySubstitution(matcher));

        return ToolBox.renameVariablesInRule(IGeneralizedRule.create(
            (TRSFunctionApplication) newLeft, newRight, newCondition), this.ng);
    }
}
