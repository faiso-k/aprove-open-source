package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Application of an int function
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolFuncApp extends SMTLIBFuncApp<SMTLIBBoolValue> implements SMTLIBBoolValue {

    private final SMTLIBBoolFunction func;

    private SMTLIBBoolFuncApp(final SMTLIBBoolFunction func, final List<SMTLIBValue> domVals) {
        super(domVals);
        this.func = func;
    }

    public static SMTLIBBoolFuncApp create(final SMTLIBBoolFunction func, final List<SMTLIBValue> domVals) {
        return new SMTLIBBoolFuncApp(func, domVals);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBoolFuncApp createFromInstance(final List<SMTLIBValue> newVals) {
        return SMTLIBBoolFuncApp.create(this.getFunc(), newVals);
    }

    @Override
    public SMTLIBBoolFunction getFunc() {
        return this.func;
    }
}
