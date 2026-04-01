package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Temporarily removes terms.
 * @author Matthias Hoelzel
 *
 */
public class IRSwTTempRemoveTermFilterProcessor extends IRSwTTempRemoveIntFilterProcessor {
    @Override
    protected AbstractFilter createFilter(final IRSwTProblem irswt, final SortDictionary dict) {
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        return new RemoveTermFilter(irswt.getRules(), dict, fng);
    }
}
