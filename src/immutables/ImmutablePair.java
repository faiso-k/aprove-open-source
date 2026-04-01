package immutables;

/**
 * This class is not really immutable, but it checks whether it has been modified whenever one of its methods is called 
 * (at least in the immutables project).
 * @param <A> The first component's type.
 * @param <B> The second component's type.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public class ImmutablePair<A, B> implements Immutable {

    /**
     * The first component.
     */
    public final A x;

    /**
     * The second component.
     */
    public final B y;

    /**
     * Cache for the hash.
     */
    private final int hashCode;

    /**
     * Creates an immutable pair.
     * @param first The first component.
     * @param second The second component.
     */
    public ImmutablePair(final A first, final B second) {
        this.x = first;
        this.y = second;
        int hashCode = first == null ? 348219013 : 78921321 * first.hashCode();
        hashCode += second == null ? 49830289 : 891341273 * second.hashCode();
        this.hashCode = hashCode;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object other) {
        if (other instanceof ImmutablePair) {
            final ImmutablePair<?, ?> pair = (ImmutablePair<?, ?>) other;
            if (this.hashCode != pair.hashCode) {
                return false;
            }
            if (this.x != pair.x) {
                if (this.x == null) {
                    return false;
                }
                if (!this.x.equals(pair.x)) {
                    return false;
                }
            }
            if (this.y != pair.y) {
                if (this.y == null) {
                    return false;
                }
                if (!this.y.equals(pair.y)) {
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
        res.append(')');
        return res.toString();
    }

}
