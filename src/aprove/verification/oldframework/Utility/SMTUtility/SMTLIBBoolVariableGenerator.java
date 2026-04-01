package aprove.verification.oldframework.Utility.SMTUtility;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;

/**
 * Generate new SMT variables of type bool with a given prefix.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolVariableGenerator {

    protected String prefix = null;
    protected long num = 0;

    private SMTLIBBoolVariableGenerator(String prefix) {
        this.prefix = prefix;
    }

    /**
     * Create and return a new instance for the given prefix.
     */
    public static SMTLIBBoolVariableGenerator create(String prefix) {
        if (prefix != null && prefix.length() > 0) {
            return new SMTLIBBoolVariableGenerator(prefix);
        }
        return null;
    }

    /**
     * Create and return next new variable.
     */
    public synchronized SMTLIBBoolVariable getNewVariable() {
        this.num++;
        return SMTLIBBoolVariable.create(this.prefix + this.num);
    }
}
