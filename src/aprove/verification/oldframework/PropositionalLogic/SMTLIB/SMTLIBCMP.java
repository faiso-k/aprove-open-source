/**
 * @author marc
 */
package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;


public abstract class SMTLIBCMP<T extends SMTLIBValue> implements SMTLIBBoolValue {

    private final T lhs;
    private final T rhs;

    protected SMTLIBCMP(final T a, final T b) {
        this.lhs = a;
        this.rhs = b;
    }

    /**
     * @param lhs lhs of the comparison
     * @param rhs rhs of the comparison
     * @return a new instance of the relation this was called on, with the
     *  given parameters as new lhs/rhs. Consequently, only the type of the
     *  relation is kept, not the arguments.
     */
    public abstract SMTLIBCMP<T> createFromExisting(T lhs, T rhs);

    @Override
    public void apply(final SMTFormulaVisitor<?> visitor) {
        visitor.caseSMTCMP(this);
        this.lhs.apply(visitor);
        this.rhs.apply(visitor);
    }

    public T getA() {
        return this.lhs;
    }

    public T getB() {
        return this.rhs;
    }
}
