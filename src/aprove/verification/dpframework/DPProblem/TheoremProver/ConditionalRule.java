package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

/**
 * @author micpar
 * @version $Id$
 */
public class ConditionalRule {

    private final ImmutableList<Rule> conditions;
    private final Rule                rule;

    /*
     * Getters
     */

    /**
     * @return Rule lhs
     */
    public TRSFunctionApplication getLeft() {
        if (this.rule != null) {
            return this.rule.getLeft();
        }
        return null;
    }

    /**
     * @return Rule rhs
     */
    public TRSTerm getRight() {
        if (this.rule != null) {
            return this.rule.getRight();
        }
        return null;
    }

    /**
     * @return The encapsulated conditions
     */
    public ImmutableList<Rule> getConditions() {
        return this.conditions;
    }

    /**
     * @return The encapsulated Rule
     */
    public Rule getRule() {
        return this.rule;
    }

    /**
     * @param forbiddenVars
     * @return new ConditionalRule with different variables
     */
    public ConditionalRule renameVars(Set<TRSVariable> forbiddenVars) {
        Rule newRule = this.rule.renameVariables(forbiddenVars);
        TRSSubstitution sigma = this.rule.getLeft().getMatcher(newRule.getLeft());
        List<Rule> newConditions = new ArrayList<Rule>();
        if (this.conditions != null) {
            for (Rule rule : this.conditions) {
                newConditions.add(Rule.create(rule.getLeft().applySubstitution(sigma), rule.getRight().applySubstitution(sigma)));
            }
            return ConditionalRule.create(ImmutableCreator.create(newConditions), newRule);
        }
        else {
            return ConditionalRule.create(newRule);
        }
    }

    /*
     * Constructors and create methods
     */

    private ConditionalRule(ImmutableList<Rule> conditions, Rule rule) {
        this.conditions = conditions;
        this.rule = rule;
    }

    /**
     * Take new Rule and create ConditionalRule without conditions
     *
     * @param rule
     * @return new ConditionalRule
     */
    public static ConditionalRule create(Rule rule) {
        return new ConditionalRule(null, rule);
    }

    /**
     * Takes new Rule and Set of Rule and creates a ConditionalRule
     *
     * @param conditions
     * @param rule
     * @return ConditionalRule with conditions set as preconditions
     */
    public static ConditionalRule create(ImmutableList<Rule> conditions, Rule rule) {
        return new ConditionalRule(conditions, rule);
    }

    /**
     * Converts a normal rule set to a conditional rule set
     *
     * @param rules
     * @return Immutable set of ConditionalRule
     */
    public static ImmutableSet<ConditionalRule> create(ImmutableSet<Rule> rules) {
        Set<ConditionalRule> condRules = new LinkedHashSet<ConditionalRule>();
        for (Rule rule : rules) {
            condRules.add(ConditionalRule.create(rule));
        }
        return ImmutableCreator.create(condRules);
    }

    /**
     * Returns the set of rules contained in this set of conditional rules.
     * CAUTION: Preconditions are omitted.
     *
     * @param condRules
     * @return Set of rules contained in conditional rule set
     */
    public static ImmutableSet<Rule> unwrap(ImmutableSet<ConditionalRule> condRules) {
        Set<Rule> rules = new LinkedHashSet<Rule>();
        for (ConditionalRule condRule : condRules) {
            rules.add(condRule.rule);
        }
        return ImmutableCreator.create(rules);
    }

    /**
     * String representation of the conditional rule.
     */
    @Override
    public String toString() {
        StringBuilder buffer = new StringBuilder();
        buffer.append("\n");
        if (this.conditions != null) {
            for (Rule cond : this.conditions) {
                buffer.append(cond);
                buffer.append(", ");
            }
            if (buffer.length() >= 2) {
                buffer.deleteCharAt(buffer.length() - 1);
                buffer.deleteCharAt(buffer.length() - 1);
                buffer.append(" | ");
            }
        }
        buffer.append(this.rule);
        return buffer.toString();
    }

    /**
     * @return hashcode
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.conditions == null) ? 0 : this.conditions.hashCode());
        result = prime * result + ((this.rule == null) ? 0 : this.rule.hashCode());
        return result;
    }

    /**
     * Reimplementation of the equals method using the base class equals
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ConditionalRule other = (ConditionalRule) obj;
        if (this.conditions == null) {
            if (other.conditions != null) {
                return false;
            }
        }
        else if (!this.conditions.equals(other.conditions)) {
            return false;
        }
        if (this.rule == null) {
            if (other.rule != null) {
                return false;
            }
        }
        else if (!this.rule.equals(other.rule)) {
            return false;
        }
        return true;
    }

}
