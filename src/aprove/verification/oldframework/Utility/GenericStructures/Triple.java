/*
 * Created on 09.02.2004
 */
package aprove.verification.oldframework.Utility.GenericStructures;


/**
 * @author thiemann
 * Attention Empty Constructor, get- and set-Methods are need for XML export.
 */
public class Triple<X, Y, Z> {

    public X x;
    public Y y;
    public Z z;

    public Triple() {
        this(null, null, null);
    }

    public Triple(final X x, final Pair<Y, Z> p) {
        this(x, p.x, p.y);
    }

    public Triple(final X x, final Y y, final Z z) {
        this.x = x;
        this.y = y;
        this.z = z;
    }

    @Override
    public String toString() {
        return ("(" + this.x + ", " + this.y + ", " + this.z + ")");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.x == null) ? 0 : this.x.hashCode());
        result = prime * result + ((this.y == null) ? 0 : this.y.hashCode());
        result = prime * result + ((this.z == null) ? 0 : this.z.hashCode());
        return result;
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
        final Triple other = (Triple) obj;
        if (this.x == null) {
            if (other.x != null) {
                return false;
            }
        } else if (!this.x.equals(other.x)) {
            return false;
        }
        if (this.y == null) {
            if (other.y != null) {
                return false;
            }
        } else if (!this.y.equals(other.y)) {
            return false;
        }
        if (this.z == null) {
            if (other.z != null) {
                return false;
            }
        } else if (!this.z.equals(other.z)) {
            return false;
        }
        return true;
    }

    public X getX() {
        return this.x;
    }

    public void setX(final X x) {
        this.x = x;
    }

    public Y getY() {
        return this.y;
    }

    public void setY(final Y y) {
        this.y = y;
    }

    public Z getZ() {
        return this.z;
    }

    public void setZ(final Z z) {
        this.z = z;
    }

}
