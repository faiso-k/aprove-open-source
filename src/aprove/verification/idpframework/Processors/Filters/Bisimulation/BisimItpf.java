package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.Itpf.*;

/**
 * Convenience class to represent possibly bisimilar Itpfs.
 * @author MP
 */
public class BisimItpf implements BisimObject {

    /** The wrapped formula. */
    private final Itpf formula;

    /** @param c formula to wrap. */
    public BisimItpf(final Itpf f) {
        this.formula = f;
    }

    /** @return the wrapped formula. */
    public Itpf getFormula() {
        return this.formula;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.formula.hashCode();
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
        final BisimItpf other = (BisimItpf) obj;
        if (this.formula == null) {
            if (other.formula != null) {
                return false;
            }
        } else if (!this.formula.equals(other.formula)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "Clause: " + this.formula;
    }
}
