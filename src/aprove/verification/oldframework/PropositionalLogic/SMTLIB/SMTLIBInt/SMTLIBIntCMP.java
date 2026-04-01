package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Base class for comparison between two ints
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBIntCMP extends SMTLIBCMP<SMTLIBIntValue> {

    protected SMTLIBIntCMP(final SMTLIBIntValue a, final SMTLIBIntValue b) {
        super(a, b);
    }

}
