package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;

/**
 * Retains only arguments that are of sort INT.
 * @author Matthias Hoelzel
 *
 */
public class IRSwTRetainIntFilterProcessor extends IRSwTAbstractSortFilterProcessor {
    @Override
    protected AbstractFilter createFilter(final IRSwTProblem irswt, final SortDictionary dict) {
        return new RetainIntFilter(irswt.getRules(), dict);
    }
}
