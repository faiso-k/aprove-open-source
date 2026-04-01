package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Base class for comparison between two bitvectors
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBBVCMP extends SMTLIBCMP<SMTLIBBVValue> {

    protected SMTLIBBVCMP(final SMTLIBBVValue a, final SMTLIBBVValue b) {
        super(a, b);
    }

}
