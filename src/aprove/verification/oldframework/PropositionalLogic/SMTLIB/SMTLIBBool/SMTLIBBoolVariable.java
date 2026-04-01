package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Variable of type bool
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolVariable extends SMTLIBVariable<SMTLIBBoolValue> implements SMTLIBBoolValue {
    private Boolean result;

    private SMTLIBBoolVariable(final String name) {
        super(name);
        this.result = null;
    }

    public static SMTLIBBoolVariable create(final String name) {
        return new SMTLIBBoolVariable(name);
    }

    @Override
    public String getTypeAsString(final SMTTypeTranslator types) {
        return types.bools();
    }

    @Override
    public void setResult(final String entry) {
        this.result = Boolean.parseBoolean(entry);
    }

    public Boolean getResultAsBoolean() {
        return this.result;
    }

}
