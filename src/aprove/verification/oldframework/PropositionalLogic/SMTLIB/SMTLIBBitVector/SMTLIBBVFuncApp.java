package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Application of an int function
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVFuncApp extends SMTLIBFuncApp<SMTLIBBVValue> {

    private final SMTLIBBVFunction func;
    private final int len;

    private SMTLIBBVFuncApp(final SMTLIBBVFunction func, final List<SMTLIBValue> domVals, final int len) {
        super(domVals);
        this.func = func;
        this.len = len;
    }

    public static SMTLIBBVFuncApp create(final SMTLIBBVFunction func, final List<SMTLIBValue> domVals, final int len) {
        return new SMTLIBBVFuncApp(func, domVals, len);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVFuncApp createFromInstance(final List<SMTLIBValue> newVals) {
        return SMTLIBBVFuncApp.create(this.getFunc(), newVals, this.getLen());
    }

    @Override
    public SMTLIBBVFunction getFunc() {
        return this.func;
    }

    public int getLen() {
        return this.len;
    }

}
