package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * True
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolTrue extends SMTLIBConstant<SMTLIBBoolValue> implements SMTLIBBoolValue  {

    private static SMTLIBBoolTrue thisInstance = new SMTLIBBoolTrue();

    private SMTLIBBoolTrue() {
    }

    public static SMTLIBBoolTrue create() {
        return SMTLIBBoolTrue.thisInstance;
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        visitor.caseTrue(this);
        return null;
    }

    @Override
    public String toString() {
        return "T";
    }

}
