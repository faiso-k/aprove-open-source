package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Relatively high-level visitor for SMTLIB theory atoms. The visitor does not
 * need to handle the run through the structure, this is done by the structure
 * itself. It only needs to concern itself with the five different groups of
 * values in a SMT formula.
 *
 * @param <R> the type of return values
 * @author Marc Brockschmidt
 */
public interface SMTFormulaVisitor<R> extends
        FormulaVisitor<Object, SMTLIBTheoryAtom> {
    /**
     * Is called in case a constant is encountered in the formula.
     * @param constant the constant.
     */
    void caseSMTConstant(SMTLIBConstant<?> constant);

    /**
     * Is called in case a variable is encountered in the formula.
     * @param var the variable.
     */
    void caseSMTVariable(SMTLIBVariable<?> var);

    /**
     * Is called in case some n-ary function like integer addition or bit
     * vector concatenation is encountered in the formula.
     * @param nAryFunc the function.
     */
    void caseSMTNAryFunc(SMTLIBNAryFunc<?> nAryFunc);

    /**
     * Is called in case an application of a user-defined function is
     * encountered in the formula.
     * @param funcApp the function application.
     */
    void caseSMTFuncApp(SMTLIBFuncApp<?> funcApp);

    /**
     * Is called in case a comparison is encountered in the formula.
     * @param comparison the comparison.
     */
    void caseSMTCMP(SMTLIBCMP<?> comparison);

    /**
     * Is called in case an if-then-else construct is encountered in the
     * formula.
     * @param ite the if-then-else.
     */
    void caseSMTITE(SMTLIBITE<?> ite);
}
