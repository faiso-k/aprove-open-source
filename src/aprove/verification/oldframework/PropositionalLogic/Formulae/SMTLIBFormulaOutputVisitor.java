package aprove.verification.oldframework.PropositionalLogic.Formulae;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;

/**
 * Interface implemented by SMTLIB visitors that produce output (usually for
 * the different SMT solvers).
 *
 * @author Marc Brockschmidt
 */
public interface SMTLIBFormulaOutputVisitor extends SMTLIBFormulaVisitor {
    /**
     * Handle some constraint.
     * @param f the new constraint
     */
    void handleConstraint(Formula<SMTLIBTheoryAtom> f);

    /**
     * @return the output string build until now.
     */
    String getResult();

    /**
     * @return a map that connects internal objects to names used in the
     *  String output. DO NOT MODIFY!
     */
    SMTLIBVarNameMap getVarNameMap();
}
