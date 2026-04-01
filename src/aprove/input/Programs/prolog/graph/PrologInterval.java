package aprove.input.Programs.prolog.graph;

import java.math.*;

import org.json.*;

import aprove.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * @author cryingshadow
 * Represents intervals used in Prolog graphs.
 */
public class PrologInterval implements Immutable, JSONExport {

    /**
     * The lower bound. Null means -infinity.
     */
    private final BigInteger lower;

    /**
     * The upper bound. Null means +infinity.
     */
    private final BigInteger upper;

    /**
     * Constructs an interval from -infinity to +infitiy.
     */
    public PrologInterval() {
        this(null, null);
    }

    /**
     * Constructs a concrete interval representing the specified value.
     * @param value The value.
     */
    public PrologInterval(final BigInteger value) {
        this(value, value);
    }

    /**
     * Standard constructor.
     * @param l The lower bound.
     * @param u The upper bound.
     */
    public PrologInterval(final BigInteger l, final BigInteger u) {
        if (Globals.useAssertions) {
            assert (l == null || u == null || l.compareTo(u) <= 0) : "Lower bound is bigger than upper bound!";
        }
        this.lower = l;
        this.upper = u;
    }

    /**
     * @param value The value to check.
     * @return True if the specified value is contained in the current interval.
     */
    public boolean contains(final BigInteger value) {
        return (this.getLower() == null || this.getLower().compareTo(value) <= 0)
            && (this.getUpper() == null || this.getUpper().compareTo(value) >= 0);
    }

    /**
     * @param value The value to check.
     * @return True if the specified value is contained in the current interval.
     */
    public boolean contains(final PrologInt value) {
        return this.contains(value.getValue());
    }

    /**
     * @param other The other interval.
     * @return True if the other interval is contained in the current one.
     */
    public boolean contains(final PrologInterval other) {
        if (this.getLower() != null) {
            if (other.getLower() != null && this.getLower().compareTo(other.getLower()) > 0) {
                return false;
            }
        }
        if (this.getUpper() != null) {
            if (other.getUpper() != null && this.getUpper().compareTo(other.getUpper()) < 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return The lower bound.
     */
    public BigInteger getLower() {
        return this.lower;
    }

    /**
     * @return The upper bound.
     */
    public BigInteger getUpper() {
        return this.upper;
    }

    /**
     * @param other The other interval.
     * @return True if the intersection of the current and the other interval is empty.
     */
    public boolean hasEmptyIntersection(final PrologInterval other) {
        return this.getLower() != null
            && other.getUpper() != null
            && this.getLower().compareTo(other.getUpper()) > 0
            || this.getUpper() != null
            && other.getLower() != null
            && this.getUpper().compareTo(other.getLower()) < 0;
    }

    public PrologInterval intdiv(final PrologInterval other) {
        // TODO Auto-generated method stub
        return new PrologInterval();
    }

    /**
     * This method may only be called on intervals having a non-empty intersection.
     * @param other The other interval.
     * @return The intersection of the current and the other interval.
     */
    public PrologInterval intersect(final PrologInterval other) {
        BigInteger low = this.getLower();
        if (low == null || other.getLower() != null && low.compareTo(other.getLower()) < 0) {
            low = other.getLower();
        }
        BigInteger up = this.getUpper();
        if (up == null || other.getUpper() != null && up.compareTo(other.getUpper()) > 0) {
            up = other.getUpper();
        }
        if (Globals.useAssertions) {
            assert (low == null || up == null || low.compareTo(up) <= 0) : "Intersection is empty!";
        }
        return new PrologInterval(low, up);
    }

    /**
     * @return True if the interval allows only one concrete value.
     */
    public boolean isConcrete() {
        return this.getUpper() != null && this.getLower() != null && this.getUpper().equals(this.getLower());
    }

    /**
     * @param other The other interval.
     * @return An interval representing all values obtained by subtracting a value in the other interval from a value
     *         in the current interval.
     */
    public PrologInterval minus(final PrologInterval other) {
        return this.plus(other.negate());
    }

    /**
     * @return The interval representing the negations of all values in the current interval.
     */
    public PrologInterval negate() {
        final BigInteger low;
        final BigInteger up;
        if (this.getLower() == null) {
            up = null;
        } else {
            up = this.getLower().negate();
        }
        if (this.getUpper() == null) {
            low = null;
        } else {
            low = this.getUpper().negate();
        }
        return new PrologInterval(low, up);
    }

    /**
     * @param other The other interval.
     * @return An interval representing all values obtained by adding two values from the current and the other
     *         interval.
     */
    public PrologInterval plus(final PrologInterval other) {
        final BigInteger low;
        final BigInteger up;
        if (this.getLower() == null || other.getLower() == null) {
            low = null;
        } else {
            low = this.getLower().add(other.getLower());
        }
        if (this.getUpper() == null || other.getUpper() == null) {
            up = null;
        } else {
            up = this.getUpper().add(other.getUpper());
        }
        return new PrologInterval(low, up);
    }

    public PrologInterval times(final PrologInterval other) {
        // TODO Auto-generated method stub
        return new PrologInterval();
    }

    @Override
    public JSONArray toJSON() {
        return
            new JSONArray(
                new Object[]{
                    this.lower == null ? "-inf" : this.lower.toString(),
                    this.upper == null ? "inf" : this.upper.toString()
                }
            );
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return (this.getLower() == null ? "(-inf" : "[" + this.getLower().toString())
            + ","
            + (this.getUpper() == null ? "+inf)" : this.getUpper().toString() + "]");
    }

}
