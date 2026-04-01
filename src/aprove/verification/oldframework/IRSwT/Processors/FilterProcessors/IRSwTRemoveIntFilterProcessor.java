package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Removes predefined arithmetic.
 * @author Matthias Hoelzel
 *
 */
public class IRSwTRemoveIntFilterProcessor extends IRSwTAbstractSortFilterProcessor {
    @Override
    protected AbstractFilter createFilter(final IRSwTProblem irswt, final SortDictionary dict) {
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        return new RemoveIntFilter(irswt.getRules(), dict, fng);
    }
}
