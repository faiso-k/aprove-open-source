package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * RulePositions are useful to reduce multiple complex code.
 *
 * @author Matthias Hoelzel
 */
class RulePosition {
    /**
     * Position
     */
    private final Position p;

    /**
     * Left or right?
     */
    private final boolean left;

    /**
     * Constructor
     *
     * @param pos Position
     * @param isLeft Boolean
     */
    public RulePosition(final Position pos, final boolean isLeft) {
        this.p = pos;
        this.left = isLeft;
    }

    /**
     * Calculates all direct rule position.
     *
     * @param rule GeneralizedRule
     * @return set of rule positions
     */
    public static Set<RulePosition> getDirectRulePositions(final GeneralizedRule rule) {
        if (rule == null || rule.getRight().isVariable()) {
            return null;
        }
        final Set<RulePosition> result = new LinkedHashSet<RulePosition>();
        for (int i = 0; i < rule.getLeft().getRootSymbol().getArity(); i++) {
            result.add(new RulePosition(Position.create(i), true));
        }
        final TRSTerm right = rule.getRight();
        if (right instanceof TRSFunctionApplication) {
            final TRSFunctionApplication rightFunc = (TRSFunctionApplication) right;
            for (int i = 0; i < rightFunc.getRootSymbol().getArity(); i++) {
                result.add(new RulePosition(Position.create(i), false));
            }
        }
        return result;
    }

    @Override
    public boolean equals(final Object other) {
        if (other == null)  {
            return false;
        } else {
            if (!(other instanceof RulePosition)) {
                return false;
            }
            final RulePosition otherPos = (RulePosition) other;
            return this.left == otherPos.left && this.p.equals(otherPos.p);
        }
    }

    @Override
    public int hashCode() {
        return this.p.hashCode() * 23 + ((this.left) ? (1) : (0));
    }

    /**
     * Returns the position.
     * @return Position.
     */
    public Position getPosition() {
        return this.p;
    }

    /**
     * Left or right?
     *
     * @return Boolean
     */
    public boolean isLeft() {
        return this.left;
    }

    /**
     * Returns the argument.
     *
     * @param rule GeneralizedRule
     * @return Term
     */
    public TRSTerm applyToRule(final GeneralizedRule rule) {
        TRSTerm t = null;
        if (this.left) {
            t = rule.getLeft();
        } else {
            t = rule.getRight();
        }

        final TRSTerm result = t.getSubtermOrNull(this.p);
        return result;
    }

    /**
     * Replaces the [rule]'s argument at [this] by [term]
     * @param rule GeneralizedRule
     * @param term the new argument
     * @return GeneralizedRule
     */
    public GeneralizedRule updateRule(final GeneralizedRule rule, final TRSTerm term) {
        if (rule == null || term == null) {
            return null;
        }
        TRSFunctionApplication leftFunc = rule.getLeft();
        TRSTerm rightTerm = rule.getRight();
        if (this.left) {
            final TRSTerm newLeft = leftFunc.replaceAt(this.p, term);
            if (newLeft.isVariable()) {
                return null;
            }
            leftFunc = (TRSFunctionApplication) newLeft;
        } else {
            rightTerm = rightTerm.replaceAt(this.p, term);
        }
        return GeneralizedRule.create(leftFunc, rightTerm);
    }

    @Override
    public String toString() {
        final String prefix = this.left ? "Left" : "Right";
        return prefix + this.p.toString();
    }
}
