/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

/**
 * Representation of values in our symbolic interpretation.
 */
public abstract class AbstractVariable implements Cloneable {
    /**
     * Returns a deep (!) copy of this {@link AbstractVariable} object.
     * @return Deep copy of this object
     */
    @Override
    public AbstractVariable clone() {
        AbstractVariable clone;
        try {
            clone = (AbstractVariable) super.clone();
        } catch (final CloneNotSupportedException e) {
            // This should never, ever happen
            return null;
        }
        return clone;
    }

    /**
     * @return true if this is the NULL instance.
     */
    public abstract boolean isNULL();
}
