package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;

/** Interface for term translators.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public abstract class TermTranslator extends Translator.TranslatorSkeleton implements TermSource, Translator {

    /** Program that is the context of this translator.
     */
    protected Program context;
    /** Term that is the state of this translator.
     */
    protected AlgebraTerm term;

    @Override
    public AlgebraTerm getTerm() {
    return this.term;
    }

    /** Sets the context for this translator.
     * @param context Program that is used as context for this translator.
     * @see Program
     */
    public void setContext(Program context) {
    this.context = context;
    }

}
