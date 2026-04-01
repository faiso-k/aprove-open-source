package aprove.verification.oldframework.Utility.SMTUtility;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Generate new SMT variables of type bitvector with a given prefix.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVVariableGenerator {

    protected String prefix = null;
    protected int len = 0;
    protected long num = 0;

    private SMTLIBBVVariableGenerator(String prefix, int len) {
        this.prefix = prefix;
        this.len = len;
    }

    /**
     * Create and return a new instance for the given prefix.
     */
    public static SMTLIBBVVariableGenerator create(String prefix, int len) {
        if (prefix != null && prefix.length() > 0) {
            return new SMTLIBBVVariableGenerator(prefix, len);
        }
        return null;
    }

    /**
     * Create and return next new variable.
     * unsynchronized!
     */
    public SMTLIBBVVariable getNewVariable() {
        this.num++;
        return SMTLIBBVVariable.create(this.prefix + this.num, this.len);
    }
}
