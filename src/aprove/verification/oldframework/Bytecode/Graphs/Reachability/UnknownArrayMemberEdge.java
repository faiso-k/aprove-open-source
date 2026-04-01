package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import immutables.*;

/**
 * Label for edges connecting abstract arrays on the heap with other objects.
 *
 * @author Marc Brockschmidt
 */
public final class UnknownArrayMemberEdge extends HeapEdge implements Immutable {
    /**
     * The only instance we ever need.
     */
    public static final UnknownArrayMemberEdge INSTANCE = new UnknownArrayMemberEdge();

    /**
     * We only need a single instance.
     */
    private UnknownArrayMemberEdge() {
    }

    /** {@inheritDoc} */
    @Override
    public String getIdentifier() {
        return "arr[?]";
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.getIdentifier();
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return 31;
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
        return null;
    }
}
