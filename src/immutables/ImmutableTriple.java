package immutables;

/**
 * This class is not really immutable, but it checks whether it has been modified whenever one of its methods is called 
 * (at least in the immutables project).
 * @param <A> The first component's type.
 * @param <B> The second component's type.
 * @param <C> The third component's type.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public class ImmutableTriple<A, B, C> implements Immutable {

    /**
     * The first component.
     */
    public final A x;

    /**
     * The second component.
     */
    public final B y;

    /**
     * The third component.
     */
    public final C z;

    /**
     * Cache for the hash.
     */
    private final int hashCode;

    /**
     * Creates an immutable triple.
     * @param first The first component.
     * @param second The second component.
     * @param third The third component.
     */
    public ImmutableTriple(final A first, final B second, final C third) {
        this.x = first;
        this.y = second;
        this.z = third;
        int hashCode = first == null ? 32121 : 809243 * first.hashCode();
        hashCode += second == null ? 5430289 : 8321431 * second.hashCode();
        hashCode += third == null ? 490123 : 123809 * third.hashCode();
        this.hashCode = hashCode;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object other) {
        if (other instanceof ImmutableTriple) {
            final ImmutableTriple<?, ?, ?> triple = (ImmutableTriple<?, ?, ?>) other;
            if (this.hashCode != triple.hashCode) {
                return false;
            }
            if (this.x != triple.x) {
                if (this.x == null) {
                    return false;
                }
                if (!this.x.equals(triple.x)) {
                    return false;
                }
            }
            if (this.y != triple.y) {
                if (this.y == null) {
                    return false;
                }
                if (!this.y.equals(triple.y)) {
                    return false;
                }
            }
            if (this.z != triple.z) {
                if (this.z == null) {
                    return false;
                }
                if (!this.z.equals(triple.z)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        res.append('(');
        res.append(this.x);
        res.append(", ");
        res.append(this.y);
        res.append(", ");
        res.append(this.z);
        res.append(')');
        return res.toString();
    }

}
