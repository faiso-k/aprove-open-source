package aprove.verification.dpframework.Utility;

import aprove.verification.oldframework.Utility.*;

/**
 * Generator for new names.
 *
 * <p>Generates a new name for an arbitrary name.</p>
 */
public interface NameGenerator {
    /**
     * Generates a new name considered unused by the FreshNameChecker
     *
     * The NameGenerator may use the old String as a base to generate a new
     * name, but it is not obliged to do so. Also, the results are not
     * necessarily reproducible; it is the job of {@link FreshNameChecker}s like
     * the {@link FreshNameGenerator} to store the results.
     */
    String getNewName(String old, FreshNameChecker fne);
}
