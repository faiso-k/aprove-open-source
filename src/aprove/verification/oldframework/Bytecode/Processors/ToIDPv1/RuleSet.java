package aprove.verification.oldframework.Bytecode.Processors.ToIDPv1;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * Convenience class to hold either sets of Rules, GeneralizedRules or
 * IGeneralizedRules.
 * @author Marc Brockschmidt
 */
public class RuleSet implements Exportable, Iterable<Rule> {
    /**
     * The enclosed rules.
     */
    private final Collection<Rule> rules;

    /**
     * @param rs the rules.
     */
    public RuleSet(final Collection<Rule> rs) {
        this.rules = rs;
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o) {
        return o.set(this.rules, Export_Util.RULES);
    }

    @Override
    public Iterator<Rule> iterator() {
        return this.rules == null ?
            java.util.Collections.<Rule>emptySet().iterator() :
                this.rules.iterator();
    }
}
