package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Basic theory atom for SMTLib formulas.
 *
 * @author Andreas Kelle-Emden
 */
public interface SMTLIBTheoryAtom extends TheoryProposition {
    Object apply(SMTLIBFormulaVisitor visitor);

    /**
     * Applies the visitor to every atom and the wrapped sub-atoms.
     * @param visitor the visitor that is called for the atoms.
     */
    void apply(SMTFormulaVisitor<?> visitor);
}
