package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Temporarily removes predefined arithmetic.
 * @author Matthias Hoelzel
 */
public class IRSwTTempRemoveIntFilterProcessor extends IRSwTTempSortFilterProcessor {
    @Override
    protected AbstractFilter createFilter(final IRSwTProblem irswt, final SortDictionary dict) {
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        return new RemoveIntFilter(irswt.getRules(), dict, fng);
    }
}
