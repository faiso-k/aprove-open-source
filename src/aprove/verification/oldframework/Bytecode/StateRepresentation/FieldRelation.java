package aprove.verification.oldframework.Bytecode.StateRepresentation;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Convenience class to encode relations that consider a field value.
 *
 * @author Marc Brockschmidt
 */
public class FieldRelation {
    /** The actual checked field. */
    private final FieldIdentifier fieldInRelation;
    /** The type of relation checked. */
    private final IntegerRelationType relationType;
    /** The reference against which we check. */
    private final AbstractVariableReference relatedReference;

    /**
     * @param fieldInRel field used in relation
     * @param relType type of the relation
     * @param relRef the related reference
     */
    public FieldRelation(final FieldIdentifier fieldInRel, final IntegerRelationType relType, final AbstractVariableReference relRef) {
        this.fieldInRelation = fieldInRel;
        this.relationType = relType;
        this.relatedReference = relRef;
    }

    /**
     * @return the fieldInRelation
     */
    public FieldIdentifier getFieldInRelation() {
        return this.fieldInRelation;
    }

    /**
     * @return the reference against which we check
     */
    public AbstractVariableReference getRelatedReference() {
        return this.relatedReference;
    }

    /**
     * @return the relationType
     */
    public IntegerRelationType getRelationType() {
        return this.relationType;
    }

    @Override
    public String toString() {
        return this.fieldInRelation + " " + this.relationType + " " + this.relatedReference;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.fieldInRelation == null) ? 0 : this.fieldInRelation.hashCode());
        result = prime
                * result
                + ((this.relatedReference == null) ? 0 : this.relatedReference.hashCode());
        result = prime * result
                + ((this.relationType == null) ? 0 : this.relationType.hashCode());
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
        if (!(obj instanceof FieldRelation)) {
            return false;
        }
        final FieldRelation other = (FieldRelation) obj;
        if (this.fieldInRelation == null) {
            if (other.fieldInRelation != null) {
                return false;
            }
        } else if (!this.fieldInRelation.equals(other.fieldInRelation)) {
            return false;
        }
        if (this.relatedReference == null) {
            if (other.relatedReference != null) {
                return false;
            }
        } else if (!this.relatedReference.equals(other.relatedReference)) {
            return false;
        }
        if (this.relationType != other.relationType) {
            return false;
        }
        return true;
    }

}
