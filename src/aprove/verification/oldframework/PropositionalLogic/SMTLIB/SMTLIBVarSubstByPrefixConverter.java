package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * Converter used to replace variables in SMTLIB theory atoms. Useful together
 * with {@link TheoryConverterVisitor}, which applies this to a complete
 * formula.
 *
 * @author Marc Brockschmidt
 */
public class SMTLIBVarSubstByPrefixConverter extends SMTLIBVarSubstConverter {
    /** The prefix to replace in variable names. */
    private final String prefixToReplace;
    /** The new prefix. */
    private final String replacementPrefix;

    /**
     * @param prefixToRepl the prefix to replace in variable names.
     * @param replacement the new prefix.
     * @param fact The factory used to create new formulae.
     */
    public SMTLIBVarSubstByPrefixConverter(
            final String prefixToRepl, final String replacement,
            final FormulaFactory<SMTLIBTheoryAtom> fact) {
        super(fact);
        this.prefixToReplace = prefixToRepl;
        this.replacementPrefix = replacement;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <T extends SMTLIBValue> T convertVariable(final SMTLIBVariable<T> var) {
        final String oldName = var.getName();
        if (oldName.startsWith(this.prefixToReplace)) {
            return (T) SMTLIBIntVariable.create(
                    this.replacementPrefix + oldName.substring(this.prefixToReplace.length()));
        } else {
            return (T) var;
        }
    }
}
