package aprove.verification.oldframework.Utility.SMTUtility;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * Generate new SMT variables of type int with a given prefix.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntVariableGenerator {

    protected String prefix = null;
    protected long num = 0;

    private SMTLIBIntVariableGenerator(String prefix) {
        this.prefix = prefix;
    }

    /**
     * Create and return a new instance for the given prefix.
     */
    public static SMTLIBIntVariableGenerator create(String prefix) {
        if (prefix != null && prefix.length() > 0) {
            return new SMTLIBIntVariableGenerator(prefix);
        }
        return null;
    }

    /**
     * Create and return next new variable.
     * unsynchronized!
     */
    public SMTLIBIntVariable getNewVariable() {
        this.num++;
        return SMTLIBIntVariable.create(this.prefix + this.num);
    }
}
