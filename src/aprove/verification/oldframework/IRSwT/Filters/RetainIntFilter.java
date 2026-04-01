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
 *
 */
public class RetainIntFilter extends SortFilter {
    /**
     * Constructor!
     * @param inputRules set of rules
     * @param dictionary sort dictionary
     */
    public RetainIntFilter(final Set<IGeneralizedRule> inputRules, final SortDictionary dictionary) {
        super(inputRules, dictionary);
    }

    /**
     * Given a term, this will filtered away terms and mixed-arguments.
     * @param t a term
     * @return a filtered term
     */
    @Override
    public TRSTerm filterTerm(final TRSTerm t) {
        return this.retainSort(t, Sort.INTEGER);
    }

    @Override
    public String export(final Export_Util eu) {
        return eu.tttext("Retained only sort INT.");
    }
}
