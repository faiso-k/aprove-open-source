package aprove.verification.oldframework.IRSwT.Orders;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.*;

/**
 * Represents some order that can be used to simplify a integer rewrite system with terms (IRSwT).
 * This is the abstract super class that defines methods to implemented by each concrete order.
 * @author Matthias Hoelzel
 */
public abstract class AbstractOrder implements Exportable {
    /** Set of all rules which have been considered when this order has been synthesized. */
    protected final Set<IGeneralizedRule> rules;

    /** Set of strict oriented rules. What strict means depends
     * on the concrete order type.*/
    protected final LinkedHashSet<IGeneralizedRule> strictRules;

    /**
     * Set of bounded rules. Again, this depends on the concrete orders.
     */
    protected final LinkedHashSet<IGeneralizedRule> boundedRules;

    /**
     * Constructor that initializes the fields
     * @param setOfRules set of considered rules
     * @param strict set of strict oriented rules
     * @param bounded set of bounded rules
     */
    public AbstractOrder(
        final Set<IGeneralizedRule> setOfRules,
        final Set<IGeneralizedRule> strict,
        final Set<IGeneralizedRule> bounded)
    {
        this.rules = new LinkedHashSet<>(setOfRules);
        this.strictRules = new LinkedHashSet<>(strict);
        this.boundedRules = new LinkedHashSet<>(bounded);
    }

    /**
     * Returns the rules.
     * @return set of rules
     */
    public Set<IGeneralizedRule> getRules() {
        return this.rules;
    }

    /**
     * Returns the rules.
     * @return set of rules
     */
    public Set<IGeneralizedRule> getStrictOrientedRules() {
        return this.strictRules;
    }

    /**
     * Returns the rules.
     * @return set of rules
     */
    public Set<IGeneralizedRule> getBoundedRules() {
        return this.boundedRules;
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        this.export(eu, sb);
        return sb.toString();
    }

    /**
     * Exports which rules are strictly decreasing and which are bounded.
     * @param sb some string builder
     * @param eu some export helper
     */
    protected final void exportStrictAndBounded(final StringBuilder sb, final Export_Util eu) {
        this.exportStrict(sb, eu);
        this.exportBounded(sb, eu);
    }

    /**
     * Exports which rules are bounded.
     * @param sb some string builder
     * @param eu some export helper
     */
    protected final void exportBounded(final StringBuilder sb, final Export_Util eu) {
        sb.append(eu.tttext("The following rules are bounded: "));
        sb.append(eu.linebreak());
        for (final IGeneralizedRule rule : this.boundedRules) {
            sb.append(rule.export(eu));
            sb.append(eu.linebreak());
        }
    }

    /**
     * Exports which rules are strictly decreasing.
     * @param sb some string builder
     * @param eu some export helper
     */
    protected final void exportStrict(final StringBuilder sb, final Export_Util eu) {
        sb.append(eu.linebreak());
        sb.append(eu.tttext("The following rules are decreasing: "));
        sb.append(eu.linebreak());
        for (final IGeneralizedRule rule : this.strictRules) {
            sb.append(rule.export(eu));
            sb.append(eu.linebreak());
        }
        sb.append(eu.linebreak());
    }

    /**
     * Gives a nice representation of this order.
     * @param eu some export helper
     * @param sb some string builder
     */
    public abstract void export(final Export_Util eu, final StringBuilder sb);
}
