package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * Base class for arithmetic functions with
 * arbitrary number of values
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBIntArithFunc extends SMTLIBNAryFunc<SMTLIBIntValue> implements SMTLIBIntValue {
    protected SMTLIBIntArithFunc(final List<SMTLIBIntValue> values) {
        super(values);
    }

    /**
     * @param vals new arguments.
     * @return a new instance of the function this was called on, with the
     *  given arguments. Consequently, only the type of the function is kept,
     *  not the arguments.
     */
    @Override
    public abstract SMTLIBIntArithFunc createFromExisting(List<SMTLIBIntValue> vals);
}
