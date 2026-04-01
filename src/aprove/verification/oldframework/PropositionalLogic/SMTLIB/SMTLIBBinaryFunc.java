package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

/**
 * Common superclass for binary functions in our SMTLIB structures.
 *
 * @param <T> the type of the operands.
 *
 * @author Marc Brockschmidt
 */
public abstract class SMTLIBBinaryFunc<T extends SMTLIBValue> extends SMTLIBNAryFunc<T> {
    /**
     * @param a first operand.
     * @param b second operand.
     */
    protected SMTLIBBinaryFunc(final T a, final T b) {
        super(a, b);
    }

    /**
     * @param a new first operand
     * @param b new second operand
     * @return a new instance of the function this was called on, with the
     *  given arguments. Consequently, only the type of the function is kept,
     *  not the arguments.
     */
    public abstract SMTLIBBinaryFunc<T> createFromExisting(final T a, final T b);

    /** {@inheritDoc} */
    @Override
    public SMTLIBBinaryFunc<T> createFromExisting(final List<T> newOpers) {
        assert (newOpers.size() == 2)
            : "Wrong number of operands for binary function";
        return this.createFromExisting(this.getA(), this.getB());
    }

    /**
     * @return the first operand.
     */
    public T getA() {
        return this.getValues().get(0);
    }

    /**
     * @return the first operand.
     */
    public T getB() {
        return this.getValues().get(1);
    }
}
