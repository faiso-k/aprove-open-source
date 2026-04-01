package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.Itpf.*;

/**
 * Convenience class to represent possibly bisimilar ItpfImplications.
 * @author MP
 */
public class BisimImplication implements BisimObject {

    /** The wrapped implication. */
    private final ItpfImplication implication;

    /** @param c implication to wrap. */
    public BisimImplication(final ItpfImplication c) {
        this.implication = c;
    }

    /** @return the wrapped implication. */
    public ItpfImplication getImplication() {
        return this.implication;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.implication.hashCode();
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
        final BisimImplication other = (BisimImplication) obj;
        if (this.implication == null) {
            if (other.implication != null) {
                return false;
            }
        } else if (!this.implication.equals(other.implication)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "IMPL: " + this.implication;
    }

}
