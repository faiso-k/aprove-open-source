package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Rewriting.*;

/** Interface for formula translators.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public abstract class FormulaTranslator extends Translator.TranslatorSkeleton implements FormulaSource, Translator {

    /** Program that is the context of this translator.
     */
    protected Program context;

    /** Sets the context for this translator.
     * @param context Program that is used as context for this translator.
     * @see Program
     */
    public void setContext(Program context) {
    this.context = context;
    }

}
