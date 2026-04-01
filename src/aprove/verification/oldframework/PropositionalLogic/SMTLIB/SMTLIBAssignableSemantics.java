package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

/**
 * Interface implemented by things which have semantics that can be assigned
 * by the SMT solver, such as variables and user-defined functions.
 *
 * @author Marc Brockschmidt
 */
public interface SMTLIBAssignableSemantics {
    /**
     * @return the name of this element.
     */
    String getName();

    /**
     * @param typeTranslator some instance providing functions that return the
     *  type string in the target language.
     * @return the type string in the target language.
     */
    String getTypeAsString(SMTTypeTranslator typeTranslator);
}
