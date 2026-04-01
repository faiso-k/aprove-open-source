package aprove.verification.oldframework.Bytecode.Processors.ToIDPv1;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * Convenience class to holding two sets of GeneralizedRules.
 * @author Marc Brockschmidt
 */
public class GeneralizedRuleSet extends RuleSet {
    /**
     * The enclosed rules.
     */
    private final Collection<GeneralizedRule> pRules;

    /**
     * The enclosed rules.
     */
    private final Collection<GeneralizedRule> rRules;

    /**
     * true iff the first set are P rules and the second R rules and this should be in the output.
     */
    private final boolean giveRuleSetsNames;

    /**
     * @param ps the P rules.
     * @param rs the P rules.
     */
    public GeneralizedRuleSet(final Collection<GeneralizedRule> ps, final Collection<GeneralizedRule> rs) {
        this(ps, rs, true);
    }

    /**
     * @param ps the P rules.
     * @param rs the P rules.
     * @param chatty true iff the first set are P rules and the second R rules and this should be in the output.
     */
    public GeneralizedRuleSet(
        final Collection<GeneralizedRule> ps,
        final Collection<GeneralizedRule> rs,
        final boolean chatty)
    {
        super(null);
        this.pRules = ps;
        this.rRules = rs;
        this.giveRuleSetsNames = chatty;
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        if (this.pRules != null) {
            if (this.giveRuleSetsNames) {
                res.append("P rules:" + o.linebreak());
            }
            for (final GeneralizedRule r : this.pRules) {
                res.append(r.export(o)).append(o.linebreak());
            }
        }
        if (this.rRules != null) {
            if (this.giveRuleSetsNames) {
                res.append("R rules:" + o.linebreak());
            }
            for (final GeneralizedRule r : this.rRules) {
                res.append(r.export(o)).append(o.linebreak());
            }
        }
        return res.toString();
    }
}
