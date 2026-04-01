package aprove.verification.oldframework.Bytecode.Parser;

/**
 * Convenience class describing a field.
 *
 * @author Marc Brockschmidt
 */
public final class FieldIdentifier {
    /**
     * The name of the enclosing class.
     */
    private final ClassName className;

    /**
     * The name of this field.
     */
    private final String fieldName;

    /**
     * @param cName name of the enclosing class.
     * @param fName name of this field.
     */
    public FieldIdentifier(final ClassName cName, final String fName) {
        this.className = cName;
        this.fieldName = fName;
    }

    /**
     * @return the name of the enclosing class.
     */
    public ClassName getClassName() {
        return this.className;
    }

    /**
     * @return the name of the field.
     */
    public String getFieldName() {
        return this.fieldName;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.className + "." + this.fieldName;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.className == null) ? 0 : this.className.hashCode());
        result = prime * result + ((this.fieldName == null) ? 0 : this.fieldName.hashCode());
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
        if (!(obj instanceof FieldIdentifier)) {
            return false;
        }
        final FieldIdentifier other = (FieldIdentifier) obj;
        if (this.className == null) {
            if (other.className != null) {
                return false;
            }
        } else if (!this.className.equals(other.className)) {
            return false;
        }
        if (this.fieldName == null) {
            if (other.fieldName != null) {
                return false;
            }
        } else if (!this.fieldName.equals(other.fieldName)) {
            return false;
        }
        return true;
    }
}
