package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * False
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolFalse extends SMTLIBConstant<SMTLIBBoolValue> implements SMTLIBBoolValue {

    private static SMTLIBBoolFalse thisInstance = new SMTLIBBoolFalse();

    private SMTLIBBoolFalse() {
    }

    public static SMTLIBBoolFalse create() {
        return SMTLIBBoolFalse.thisInstance;
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        visitor.caseFalse(this);
        return null;
    }

}
