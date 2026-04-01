package aprove.verification.oldframework.IRSwT.Orders;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.IRSwT.Filters.*;

/**
 * Wraps an ExportableOrder and know which rules have been oriented strictly.
 * @author Matthias Hoelzel
 *
 */
public class TermOrder extends AbstractOrder {
    /** The generated order! */
    private final ExportableOrder<TRSTerm> exportableOrder;

    /** Sometimes we apply some filter to our problem first. */
    private final AbstractFilter filter;

    /**
     * Constructor!
     * @param setOfRules set of all rules
     * @param strict set of strict oriented rules
     * @param eo some exportable term order
     * @param appliedFilter some filter or null
     */
    public TermOrder(
        final Set<IGeneralizedRule> setOfRules,
        final LinkedHashSet<IGeneralizedRule> strict,
        final ExportableOrder<TRSTerm> eo,
        final AbstractFilter appliedFilter)
    {
        super(setOfRules, strict, setOfRules);
        this.exportableOrder = eo;
        this.filter = appliedFilter;
    }

    @Override
    public void export(final Export_Util eu, final StringBuilder sb) {
        if (this.exportableOrder != null) {
            sb.append(eu.tttext("Found the following term order:"));
            sb.append(eu.linebreak());
            sb.append(this.exportableOrder.export(eu));
            sb.append(eu.linebreak());
        }
        this.exportStrict(sb, eu);

    }
}
