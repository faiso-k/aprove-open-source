package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.Itpf.*;

/**
 * Convenience class to represent possibly bisimilar ItpfConjClauses.
 * @author MP
 */
public class BisimConjClause implements BisimObject {

    /** The wrapped clause. */
    private final ItpfConjClause conjClause;

    /** @param c conjClause to wrap. */
    public BisimConjClause(final ItpfConjClause c) {
        this.conjClause = c;
    }

    /** @return the wrapped conjClause. */
    public ItpfConjClause getClause() {
        return this.conjClause;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.conjClause.hashCode();
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
        final BisimConjClause other = (BisimConjClause) obj;
        if (this.conjClause == null) {
            if (other.conjClause != null) {
                return false;
            }
        } else if (!this.conjClause.equals(other.conjClause)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "Clause: " + this.conjClause;
    }
}
