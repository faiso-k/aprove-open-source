package aprove.verification.idpframework.Algorithms.Confluence;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ConfluenceFactory {

    /**
     * this method takes a set of IRules and iterates over all critical pairs.
     * Non-root overlaps will be returned before root overlaps.
     * @param rules
     */
    public static AbortableIterator<ImmutableTriple<ITerm<?>, ITerm<?>, Boolean>> getCriticalPairs(final Set<? extends IRule> rules) {
        return new CriticalPairIterator(rules);
    }

}
