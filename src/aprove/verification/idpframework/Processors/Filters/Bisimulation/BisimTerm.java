package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.BasicStructures.*;

/**
 * Convenience class to represent possibly bisimilar terms.
 * @author MP
 */
public class BisimTerm implements BisimObject {
    /** The wrapped term. */
    private final ITerm<?> term;

    /** @param v IVariable<?> to wrap. */
    public BisimTerm(final ITerm<?> t) {
        this.term = t;
    }

    /** @return the wrapped term. */
    public ITerm<?> getTerm() {
        return this.term;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.term.hashCode();
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
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final BisimTerm other =
            (BisimTerm) obj;
        if (this.term == null) {
            if (other.term != null) {
                return false;
            }
        } else if (!this.term.equals(other.term)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "Term: " + this.term;
    }
}
