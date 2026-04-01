package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Rewriting.*;

/** Interface for program sources.
 *  <P>
 *  Implement by extending with interfaces.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public interface ProgramSource {

    /** Returns a program from this source.
     * @return Program from this source.
     * @see Program
     */
    public Program getProgram();

}
