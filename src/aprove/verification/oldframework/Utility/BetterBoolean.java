package aprove.verification.oldframework.Utility;

/**
 * A wrapper for Java's primitive <code>boolean</code>.
 * <br>
 * In contrast to <code>java.lang.Boolean</code>, the value of
 * <code>BetterBoolean</code> can be changed.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class BetterBoolean {

    private boolean value;

    /**
     * Constructor for a <code>BetterBoolean</code> that wraps <code>value</code>.
     * @param value A <code>boolean</code>.
     */
    public BetterBoolean(boolean value) {
    this.value = value;
    }

    /**
     * Returns the <code>boolean</code> that is wrapped by this instance of
     * <code>BetterBoolean</code>.
     */
    public boolean booleanValue() {
    return this.value;
    }

    /**
     * Set the <code>boolean</code> that is wrapped by this instance of
     * <code>BetterBoolean</code>.
     * @param value A <code>boolean</code>.
     */
    public void setValue(boolean value) {
    this.value = value;
    }

    /**
     * Determines whether <code>o</code> is an instance of <code>BetterBoolean</code>
     * and whether this <code>BetterBoolean</code> and the other <code>BetterBoolean</code> wrap the same <code>boolean</code>.
     * @param o An <code>Object</code>.
     */
    @Override
    public boolean equals(Object o) {
    if(o==null || !(o instanceof BetterBoolean)) {
        return false;
    }
    return this.value==((BetterBoolean)o).value;
    }

    /** Computes a hash code for this <code>BetterBoolean</code>.
     * This is the hash code of the wrapped <code>boolean</code>.
     */
    @Override
    public int hashCode() {
    return Boolean.valueOf(this.value).hashCode();
    }

    /** Returns a string representation of this <code>BetterBoolean</code>.
     * This is the string representation of the wrapped <code>boolean</code>.
     */
    @Override
    public String toString() {
    return Boolean.valueOf(this.value).toString();
    }
}
