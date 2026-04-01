package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

/**
 * SMTLIB propositional variable
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBVariable<T extends SMTLIBValue> implements SMTLIBValue, SMTLIBAssignableSemantics {
    /** The name of the variable. */
    private final String name;

    /**
     * @param n the name of the variable.
     */
    protected SMTLIBVariable(final String n) {
        this.name = n;
    }

    public abstract void setResult(String entry);

    /** {@inheritDoc} */
    @Override
    public void apply(final SMTFormulaVisitor<?> visitor) {
        visitor.caseSMTVariable(this);
    }

    /** {@inheritDoc} */
    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseSMTLIBVariable(this);
    }

    /** {@inheritDoc} */
    @Override
    public final String getName() {
        return this.name;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof SMTLIBVariable)) {
            return false;
        }
        final SMTLIBVariable<?> other = (SMTLIBVariable<?>) obj;
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        return true;
    }
}
