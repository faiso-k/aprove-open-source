package aprove.verification.oldframework.IntegerReasoning;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;

/**
 * @author Alexander Weinert
 *
 * Is thrown when adding a relation would lead to an inconsistent integer,
 * state, i.e., if the current set of constraints in conjunction with the
 * new relation is unsatisfiable.
 */
public class InconsistentStateException extends RuntimeException {
    /** The (consistent) integer state to which the new relation was to be added */
    private final IntegerState integerState;
    /** The relation whose addition would have made the integerState inconsistent */
    private final LLVMRelation newRelation;

    /**
     * @param integerState {@link InconsistentStateException#integerState}
     * @param newRelation {@link InconsistentStateException#newRelation}
     */
    public InconsistentStateException(final IntegerState integerState, final LLVMRelation newRelation) {
        this.integerState = integerState;
        this.newRelation = newRelation;
    }

    /**
     * @return {@link #integerState}
     */
    public IntegerState getIntegerState() {
        return this.integerState;
    }

    /**
     * @return {@link #newRelation}
     */
    public LLVMRelation getNewRelation() {
        return this.newRelation;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.integerState == null) ? 0 : this.integerState.hashCode());
        result = prime * result + ((this.newRelation == null) ? 0 : this.newRelation.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
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

        final InconsistentStateException other = (InconsistentStateException) obj;
        if (this.integerState == null) {
            if (other.integerState != null) {
                return false;
            }
        } else if (!this.integerState.equals(other.integerState)) {
            return false;
        }

        if (this.newRelation == null) {
            if (other.newRelation != null) {
                return false;
            }
        } else if (!this.newRelation.equals(other.newRelation)) {
            return false;
        }

        return true;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder();
        builder.append("InconsistentStateException [integerState=");
        builder.append(this.integerState);
        builder.append(", newRelation=");
        builder.append(this.newRelation);
        builder.append("]");
        return builder.toString();
    }
}
