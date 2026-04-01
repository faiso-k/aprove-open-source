/**
 *
 */
package aprove.verification.oldframework.IRSwT.Filters;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;

/**
 * Removes TERM- or MIXED-sorted arguments.
 * @author Matthias Hoelzel
 */
public class RetainTermFilter extends SortFilter {
    /**
     * Constructor!
     * @param inputRules some input rules
     * @param dictionary sort dictionary
     */
    public RetainTermFilter(final Set<IGeneralizedRule> inputRules, final SortDictionary dictionary) {
        super(inputRules, dictionary);
    }

    @Override
    public TRSTerm filterTerm(final TRSTerm t) {
        return this.retainSort(t, Sort.FUNAPP);
    }

    @Override
    public String export(final Export_Util eu) {
        return eu.tttext("Retained only sort TERM.");
    }

    @Override
    protected IGeneralizedRule processRule(final IGeneralizedRule newRule) {
        return IGeneralizedRule.create(newRule.getLeft(), newRule.getRight(), null);
    }
}
