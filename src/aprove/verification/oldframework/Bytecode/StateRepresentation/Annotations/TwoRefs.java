package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import immutables.*;

/**
 * An immutable set of two references (may be the same). This is used to represent that the two references are joining.
 * @author cotto
 */
public class TwoRefs implements Immutable {
    /**
     * A reference. It is ensured that this.refOne.compareTo(this.refTwo) <= 0
     */
    private final AbstractVariableReference refOne;
    /**
     * A reference. It is ensured that this.refOne.compareTo(this.refTwo) <= 0
     */
    private final AbstractVariableReference refTwo;

    /**
     * Create a new object for the two references.
     * @param refA a reference
     * @param refB a reference
     */
    public TwoRefs(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        assert (refA != null);
        assert (refB != null);
        if (refA.compareTo(refB) <= 0) {
            this.refOne = refA;
            this.refTwo = refB;
        } else {
            this.refOne = refB;
            this.refTwo = refA;
        }
    }

    /**
     * {@inheritDoc}
     */
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
        final TwoRefs other = (TwoRefs) obj;
        if (this.refOne == null) {
            if (other.refOne != null) {
                return false;
            }
        } else if (!this.refOne.equals(other.refOne)) {
            return false;
        }
        if (this.refTwo == null) {
            if (other.refTwo != null) {
                return false;
            }
        } else if (!this.refTwo.equals(other.refTwo)) {
            return false;
        }
        return true;
    }

    /**
     * @param ref a reference
     * @return true iff at least one of the two references if ref
     */
    public boolean forRef(final AbstractVariableReference ref) {
        return ref.equals(this.refOne) || ref.equals(this.refTwo);
    }

    /**
     * Attention: Only call this if ref is one of the two references.
     * @param ref one of the two references
     * @return the other reference
     */
    public AbstractVariableReference getOther(final AbstractVariableReference ref) {
        if (ref.equals(this.refOne)) {
            return this.refTwo;
        } else {
            return this.refOne;
        }
    }

    /**
     * @return the first of the two references
     */
    public AbstractVariableReference getRefOne() {
        return this.refOne;
    }

    /**
     * @return the second of the two references
     */
    public AbstractVariableReference getRefTwo() {
        return this.refTwo;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.refOne == null) ? 0 : this.refOne.hashCode());
        result = prime * result + ((this.refTwo == null) ? 0 : this.refTwo.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "(" + this.refOne + "," + this.refTwo + ")";
    }
}
