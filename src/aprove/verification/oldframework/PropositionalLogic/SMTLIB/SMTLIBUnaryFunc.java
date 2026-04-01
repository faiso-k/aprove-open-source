package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

/**
 * Common superclass for unary functions in our SMTLIB structures.
 *
 * @param <T> the type of the operand.
 *
 * @author Marc Brockschmidt
 */
public abstract class SMTLIBUnaryFunc<T extends SMTLIBValue> extends SMTLIBNAryFunc<T> {
    /**
     * @param op the operand.
     */
    protected SMTLIBUnaryFunc(final T op) {
        super(op);
    }

    /**
     * @param op new operand
     * @return a new instance of the function this was called on, with the
     *  given argument. Consequently, only the type of the function is kept,
     *  not the argument.
     */
    public abstract SMTLIBUnaryFunc<T> createFromExisting(final T op);

    /** {@inheritDoc} */
    @Override
    public SMTLIBUnaryFunc<T> createFromExisting(final List<T> newOpers) {
        assert (newOpers.size() == 1)
            : "Wrong number of operands for unary function";
        return this.createFromExisting(this.getA());
    }

    /**
     * @return the first operand.
     */
    public T getA() {
        return this.getValues().get(0);
    }
}
