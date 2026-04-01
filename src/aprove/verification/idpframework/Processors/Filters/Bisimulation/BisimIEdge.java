package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.IDPGraph.*;

/**
 * Convenience class to represent possibly bisimilar variables.
 * @author MP
 */
public class BisimIEdge implements
        BisimObject {
    /** The wrapped edge. */
    private final IEdge edge;

    /** @param e edge to wrap. */
    public BisimIEdge(final IEdge e) {
        this.edge = e;
    }

    /** @return the wrapped edge. */
    public IEdge getEdge() {
        return this.edge;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.edge.hashCode();
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
        final BisimIEdge other = (BisimIEdge) obj;
        if (this.edge == null) {
            if (other.edge != null) {
                return false;
            }
        } else if (!this.edge.equals(other.edge)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "Edge: " + this.edge;
    }

}

