package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Application of an int function
 *
 * @author CKuknat
 */
public class SMTLIBRatFuncApp extends SMTLIBFuncApp<SMTLIBRatValue> {

    private final SMTLIBRatFunction func;

    private SMTLIBRatFuncApp(final SMTLIBRatFunction func, final List<SMTLIBValue> domVals) {
        super(domVals);
        this.func = func;
    }

    public static SMTLIBRatFuncApp create(final SMTLIBRatFunction func, final List<SMTLIBValue> domVals) {
        return new SMTLIBRatFuncApp(func, domVals);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatFuncApp createFromInstance(final List<SMTLIBValue> newVals) {
        return SMTLIBRatFuncApp.create(this.getFunc(), newVals);
    }

    @Override
    public SMTLIBRatFunction getFunc() {
        return this.func;
    }
}
