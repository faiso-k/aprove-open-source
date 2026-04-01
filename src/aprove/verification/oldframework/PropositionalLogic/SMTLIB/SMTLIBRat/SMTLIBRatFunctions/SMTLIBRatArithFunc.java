package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * Base class for arithmetic functions with
 * arbitrary number of values
 *
 * @author CKuknat
 */
public abstract class SMTLIBRatArithFunc extends SMTLIBNAryFunc<SMTLIBRatValue> implements SMTLIBRatValue {
    protected SMTLIBRatArithFunc(final List<SMTLIBRatValue> values) {
        super(values);
    }
}
