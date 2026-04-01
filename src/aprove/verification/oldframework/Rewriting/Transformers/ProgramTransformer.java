package aprove.verification.oldframework.Rewriting.Transformers;

import aprove.verification.oldframework.Rewriting.*;

/** Interface for a program transformer.
 * @author Stephan Falke
 * @version $Id$
 */
public interface ProgramTransformer {

    /** Transforms a program.
     * @param prog the program that is to be transformed
     */
    public Program transform(Program prog);

}
