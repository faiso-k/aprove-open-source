package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.IDPGraph.*;

/**
 * Convenience class to represent possibly bisimilar variables.
 * @author MP
 */
public class BisimINode implements
        BisimObject {
    /** The wrapped node. */
    private final INode node;

    /** @param n node to wrap. */
    public BisimINode(final INode n) {
        this.node = n;
    }

    /** @return the wrapped node. */
    public INode getNode() {
        return this.node;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.node.hashCode();
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
        final BisimINode other = (BisimINode) obj;
        if (this.node == null) {
            if (other.node != null) {
                return false;
            }
        } else if (!this.node.equals(other.node)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "Node: " + this.node;
    }

}

