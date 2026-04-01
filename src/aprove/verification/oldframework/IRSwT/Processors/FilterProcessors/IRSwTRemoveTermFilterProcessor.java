/**
 *
 */
package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Remove arguments that are always terms and replaces
 * remaining constructor symbols by 0.
 * @author Matthias Hoelzel
 *
 */
public class IRSwTRemoveTermFilterProcessor extends IRSwTAbstractSortFilterProcessor {
    @Override
    protected AbstractFilter createFilter(final IRSwTProblem irswt, final SortDictionary dict) {
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        return new RemoveTermFilter(irswt.getRules(), dict, fng);
    }
}
