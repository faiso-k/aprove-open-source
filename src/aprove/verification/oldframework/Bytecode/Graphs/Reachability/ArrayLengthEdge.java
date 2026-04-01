package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;

public class ArrayLengthEdge extends HeapEdge {
    /** {@inheritDoc} */
    @Override
    public String getIdentifier() {
        return "len";
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.getIdentifier();
    }

    @Override
    public int hashCode() {
        return 17;
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
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public NonRootPosition getNonRootPosition() {
        return ArrayLengthPosition.create(null);
    }
}
