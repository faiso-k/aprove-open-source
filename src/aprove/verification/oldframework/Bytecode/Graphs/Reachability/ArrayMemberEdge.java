package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;

/**
 * Label for edges connecting concrete arrays on the heap with other objects.
 *
 * @author Marc Brockschmidt
 */
public class ArrayMemberEdge extends HeapEdge {
    /**
     * Index referencing the other object.
     */
    private final int index;

    /**
     * @param i Index referencing the other object.
     */
    public ArrayMemberEdge(final int i) {
        this.index = i;
    }

    /** {@inheritDoc} */
    @Override
    public String getIdentifier() {
        return "arr[" + this.index + "]";
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.getIdentifier();
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.index;
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
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ArrayMemberEdge other = (ArrayMemberEdge) obj;
        if (this.index != other.index) {
            return false;
        }
        return true;
    }

    /**
     * @return the index
     */
    public int getIndex() {
        return this.index;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public NonRootPosition getNonRootPosition() {
        return ArrayElementPosition.create(null, this.index);
    }
}
