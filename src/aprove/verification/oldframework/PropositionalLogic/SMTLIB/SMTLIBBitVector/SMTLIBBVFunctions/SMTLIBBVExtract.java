package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Extract all bits b_i,...,b_j from a given bitvector.
 * We DO NOT check if the parameters (a, i, j) are correct!
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVExtract extends SMTLIBUnaryFunc<SMTLIBBVValue> implements SMTLIBBVValue {
    private final int i;
    private final int j;

    private SMTLIBBVExtract(final SMTLIBBVValue a, final int i, final int j) {
        super(a);
        this.i = i;
        this.j = j;
    }

    public static SMTLIBBVExtract create(final SMTLIBBVValue a, final int i, final int j) {
        return new SMTLIBBVExtract(a, i, j);
    }

    @Override
    public SMTLIBUnaryFunc<SMTLIBBVValue> createFromExisting(final SMTLIBBVValue op) {
        return SMTLIBBVExtract.create(op, this.i, this.j);
    }


    @Override
    public int getLen() {
        return this.j-this.i;
    }

    public int getI() {
        return this.i;
    }

    public int getJ() {
        return this.j;
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        visitor.caseBVExtract(this);
        return null;
    }
}
