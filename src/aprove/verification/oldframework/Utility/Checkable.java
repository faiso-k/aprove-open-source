package aprove.verification.oldframework.Utility;

import java.util.*;

/** A class that implements this interface will make some
 *  sanity checks in order to make debugging easier.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */


public interface Checkable {

    /** Checks for internal consistency.
     * @throws RuntimeException in case of internal inconsistencies.
     */
    public void check();

    /** Checks for internal consistency excluding objects that
     *  have already been checked.
     * @param checked Set of objects that have already been checked.
     * @throws RuntimeException in case of internal inconsistencies.
     */
    public void check(Set checked);

}
