package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

/**
 * Base interface for all value types.
 * That is basically everything...
 *
 * @author Andreas Kelle-Emden
 */
public interface SMTLIBValue {

    public Object apply(SMTLIBFormulaVisitor visitor);

    /**
     * Applies the visitor to every atom and the wrapped sub-atoms.
     * @param visitor the visitor that is called for the atoms.
     */
    void apply(SMTFormulaVisitor<?> visitor);
}
