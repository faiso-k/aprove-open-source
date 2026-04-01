package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;

import aprove.*;
import immutables.*;

/**
 * Node for the greater-equals-graph of SimplePolyConstraintSimplifier.
 * Wraps either a number (int) or an indefinite (String). You can use
 * isNumerical() to find out whether this.number or this.indefinite is
 * valid in this.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class GENode implements Immutable {

    /**
     * The number represented by this (if this.isNumerical())
     */
    public final BigInteger number;

    /**
     * The indefinite represented by this, or null if this
     * represents a number
     */
    public final String indefinite;

    private int hashValue; // cache for the hash value

    private GENode (String indefinite, BigInteger number) {
        this.indefinite = indefinite;
        this.number = number;
        this.hashValue = this.indefinite == null ? this.number.hashCode() : 623517 * this.indefinite.hashCode();
    }

    /**
     * Creates a GENode which encapsulates an indefinite.
     *
     * @param indefinite the indefinite to be encapsulated, must not be null
     * @return the corresponding GENode
     */
    public static GENode create(String indefinite) {
        if (Globals.useAssertions) {
            assert(indefinite != null);
        }
        return new GENode(indefinite, null);
    }

    /**
     * Creates a GENode which encapsulates a number.
     *
     * @param number the number to be encapsulated
     * @return the corresponding GENode
     */
    public static GENode create(BigInteger number) {
        return new GENode(null, number);
    }

    /**
     * @return true if this represents a number,
     *  false if this represents an indefinite
     */
    public boolean isNumerical() {
        return (this.indefinite == null);
    }

    @Override
    public String toString() {
        if (this.isNumerical()) {
            return this.number.toString();
        }
        else {
            return this.indefinite;
        }
    }

    @Override
    public int hashCode() {
        return this.hashValue;
    }

    @Override
    public boolean equals(Object o) {
        if (! (o instanceof GENode)) {
            return false;
        }
        GENode other = (GENode) o;
        if (this.hashValue != other.hashValue) {
            return false;
        }
        if (this.number == null ^ other.number == null) {
            return false;
        }
        if (this.number == null || this.number.equals(other.number)) {
            if (this.indefinite == null) {
                return (other.indefinite == null);
            }
            else {
                return (this.indefinite.equals(other.indefinite));
            }
        }
        else {
            return false;
        }
    }
}
