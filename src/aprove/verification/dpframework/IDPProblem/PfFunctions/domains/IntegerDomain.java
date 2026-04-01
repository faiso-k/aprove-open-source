/**
 *
 * @author noschins    ki
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions.domains;

import java.math.*;

import aprove.prooftree.Export.Utility.*;

/**
 * Utility functions for integer domains.
 *
 * Valid domains are
 *   z                     - Integers ("unrestricted integers")
 *   any positive number n - signed n-bit integer with two-complements
 *                           representation ("restricted integers")
 *
 * Two <code>Domain</code> instances are considered equal iff
 * they were created for the same suffix.
 *
 *
 * FIXME: There are probably just a few different Domain instances. So add a
 * DomainFactory for singleton pattern.
 *
 * @author noschinski
 *
 */
public class IntegerDomain extends Domain {

    /**
     * @param bits 0 iff Z, bit with otherwise
     */
    public static String generateSuffix(int bits) {
        if (bits > 0) {
            return "int_" + bits;
        } else if (bits == 0) {
            return "int";
        } else {
            throw new IllegalArgumentException("bits must be >= 0");
        }
    }


    public static int decodeSuffix(String suffix) {
        if (suffix.equals("int")) {
            return 0;
        } else if (suffix.startsWith("int_")) {
            try {
                return Integer.parseInt(suffix.substring(4));
            } catch (Exception e) {
            }
        }
        throw new IllegalArgumentException("no integer domain");
    }

    /**
     * For mathematical integers: 0. Else the number of bits used for this
     * domain in two-complements signed integer representation.
     */
    private final int bits;

    /**
     * Cached value: 2^(bits-1)
     */
    private final BigInteger twoToKm1;

    /**
     * Cached value: 2^bits
     */
    private final BigInteger twoToK;


    private IntegerDomain(int bits) {
        super(IntegerDomain.generateSuffix(bits));
        this.bits = bits;

        if (this.bits != 0) {
            this.twoToKm1 = BigInteger.ONE.shiftLeft(this.bits-1);
            this.twoToK = this.twoToKm1.shiftLeft(1);
        } else {
            this.twoToKm1 = null;
            this.twoToK = null;
        }

    }

    @Override
    public boolean isIntegerDomain() {
        return true;
    }

    /**
     * Creates a new domain instance for suffix.
     *
     * <p><strong>Unless you really know better, just use
     * {@link DomainFactory}.create</strong>, which will
     * prevent unnecessary creation of objects.</p>
     */
    protected static IntegerDomain createNew(int bits) {
        return new IntegerDomain(bits);
    }

    /**
     * Return the number of bits used for representing this integer.
     * 0 is returned mathematical integers.
     * @return
     */
    public int getBits() {
        return this.bits;
    }

    /**
     * Returns the domain suffix for this domain.
     */
    @Override
    public String getSuffix() {
        return this.suffix;
    }

    /**
     * Checks if <code>val</code> is in the range of this Domain:
     * (-2^(k-1) &lt;= val &lt; 2^(k-1) for a k-bit domain).
     */
    public boolean inRange(BigInteger val) {
        return this.bits == 0 || (val.compareTo(this.twoToKm1) < 0
                        && val.compareTo(this.twoToKm1.negate()) >= 0);
    }

    /**
     * Computes sign_k(val) with <code>k=this.getBits()</code>
     * For <code>k=0</code> this is a noop.
     *
     * FIXME: Add reference if ITRS definitions are ready.
     */
    public BigInteger sign(BigInteger val) {
        if (this.bits == 0) {
            return val;
        }
        if (val.compareTo(this.twoToKm1) >= 0 && val.compareTo(this.twoToK) < 0) {
            return val.subtract(this.twoToK);
        } else {
            return val;
        }
    }

    /**
     * Computes unsign_k(val) with <code>k=this.getBits()</code>
     * For <code>k=0</code> this is a noop.
     *
     * FIXME: Add reference if ITRS definitions are ready.
     */
    public BigInteger unsign(BigInteger val) {
        if (this.bits == 0
                || (val.signum() >= 0 && val.compareTo(this.twoToKm1) < 0)) {
            return val;
        } else {
            return val.subtract(this.twoToKm1.shiftLeft(1));
        }
    }

    /**
     * Computes castUnsigned(val) with <code>k=this.getBits()</code>
     * For <code>k=0</code> this is a noop.
     *
     * FIXME: Add reference if ITRS definitions are ready.
     */
    public BigInteger castUnsigned(BigInteger val) {
        if (this.bits == 0) {
            return val;
        } else {
            return val.mod(this.twoToK);
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.suffix == null) ? 0 : this.suffix.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IntegerDomain other = (IntegerDomain) obj;
        if (this.suffix == null) {
            if (other.suffix != null) {
                return false;
            }
        } else if (!this.suffix.equals(other.suffix)) {
            return false;
        }
        return true;
    }

    @Override
    public String export(Export_Util o) {
        return this.bits > 0 ? "Int" +this.bits : "Integer";
    }

}
