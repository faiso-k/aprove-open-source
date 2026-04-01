package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Application of an int function
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntFuncApp extends SMTLIBFuncApp<SMTLIBIntValue> {

    private final SMTLIBIntFunction func;

    private SMTLIBIntFuncApp(final SMTLIBIntFunction func, final List<SMTLIBValue> domVals) {
        super(domVals);
        this.func = func;
    }

    public static SMTLIBIntFuncApp create(final SMTLIBIntFunction func, final List<SMTLIBValue> domVals) {
        return new SMTLIBIntFuncApp(func, domVals);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntFuncApp createFromInstance(final List<SMTLIBValue> newVals) {
        return SMTLIBIntFuncApp.create(this.getFunc(), newVals);
    }

    @Override
    public SMTLIBIntFunction getFunc() {
        return this.func;
    }

}
