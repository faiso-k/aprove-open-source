package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

/**
 * Common superclass for n-ary functions in our SMTLIB structures.
 *
 * @param <T> the type of the operands.
 *
 * @author Marc Brockschmidt
 */
public abstract class SMTLIBNAryFunc<T extends SMTLIBValue> implements SMTLIBValue {
    /** The operands. */
    private final List<T> operands;

    /**
     * @param op the operand.
     */
    public SMTLIBNAryFunc(final T op) {
        this.operands = new ArrayList<T>();
        this.operands.add(op);
    }

    /**
     * @param opA first operand.
     * @param opB second operand.
     */
    protected SMTLIBNAryFunc(final T opA, final T opB) {
        this.operands = new ArrayList<T>();
        this.operands.add(opA);
        this.operands.add(opB);
    }

    /**
     * @param opers the operands.
     */
    protected SMTLIBNAryFunc(final List<T> opers) {
        this.operands = opers;
    }

    /**
     * @param newOpers new arguments.
     * @return a new instance of the function this was called on, with the
     *  given arguments. Consequently, only the type of the function is kept,
     *  not the arguments.
     */
    public abstract SMTLIBNAryFunc<T> createFromExisting(final List<T> newOpers);

    /**
     * @return the operands (values) of this function.
     */
    public List<T> getValues() {
        return this.operands;
    }

    /** {@inheritDoc} */
    @Override
    public void apply(final SMTFormulaVisitor<?> visitor) {
        visitor.caseSMTNAryFunc(this);
        for (final T op : this.operands) {
            op.apply(visitor);
        }
    }
}
