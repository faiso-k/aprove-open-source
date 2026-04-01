package aprove.verification.oldframework.Utility;

import aprove.verification.dpframework.Utility.*;


/**
 * A {@link FreshNameChecker} provides a {@link NameGenerator} with a
 * possibility to check whether a name is unused.
 */
public interface FreshNameChecker {

    /**
     * Checks whether the given name is unused.
     */
    public boolean isUnused(String name);

}
