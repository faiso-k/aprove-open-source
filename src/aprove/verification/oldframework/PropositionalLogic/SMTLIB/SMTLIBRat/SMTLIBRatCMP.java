package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Base class for comparison between two ints
 *
 * @author CKuknat
 */
public abstract class SMTLIBRatCMP extends SMTLIBCMP<SMTLIBRatValue> {
    protected SMTLIBRatCMP(final SMTLIBRatValue a, final SMTLIBRatValue b) {
        super(a, b);
    }
}
