package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Rewriting.*;

/** Interface for program prettyprinters.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public interface ProgramPrettyPrinter {

    /** Returns a prettyprinted string representation
     *  of the given program.
     * @param prog Program to prettyprint.
     * @return Prettyprinted string representation of the given program.
     */
    public String prettyPrint(Program prog);

}
