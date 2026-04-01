package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Rewriting.*;

/** Abstract implentation for program translators.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public abstract class ProgramTranslator extends Translator.TranslatorSkeleton implements ProgramSource, Translator {

    /** Program that is the state of this translator.
     */
    protected Program program;
    protected boolean variable_condition_violated = false;

    @Override
    public Program getProgram() {
    return this.program;
    }

    /** Sets the state of this translator.
     * @param program Program that replaces the state of this translator.
     */
    public void setProgram(Program program) {
    this.program = program;
    }

    public boolean getVariableConditionViolated() {
        return this.variable_condition_violated;
    }

    @Override
    public Object getState() {
    return this.getProgram();
    };

    @Override
    public void setState(Object state) {
    if (state instanceof Program) {
        this.setProgram((Program) state);
    } else {
        throw new RuntimeException("non-Program state in ProgramTranslator.setState()");
    };
    };
}
