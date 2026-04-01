/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;

/**
 * @author cotto
 * Encapsulate a BigInteger.
 */
public final class BigIntImmutable implements GPolyCoeff, SMTLIBFormatter, XMLObligationExportable, CPFAdditional {

    /**
     * For every BigInteger remember the corresponding BigIntImmutable.
     */
    private static final Map<BigInteger, BigIntImmutable> cache;

    public static final BigIntImmutable ZERO;
    public static final BigIntImmutable ONE;
    public static final BigIntImmutable TWO;
    public static final BigIntImmutable TEN;
    public static final BigIntImmutable MINUS_ONE;


    static {
        cache = new HashMap<BigInteger, BigIntImmutable>();
        ZERO = BigIntImmutable.create(BigInteger.ZERO);
        ONE = BigIntImmutable.create(BigInteger.ONE);
        TWO = BigIntImmutable.create(BigInteger.valueOf(2));
        TEN = BigIntImmutable.create(BigInteger.TEN);
        MINUS_ONE = BigIntImmutable.create(BigInteger.valueOf(-1));
    }
    /**
     * The encapsulated BigInteger object.
     */
    private final BigInteger bigInt;

    /**
     * Create a new BigIntImmutable based on the given BigInteger.
     * @param bigIntParam The BigInteger defining the new object.
     */
    private BigIntImmutable(final BigInteger bigIntParam) {
        this.bigInt = bigIntParam;
    }

    /**
     * @return the BigInteger contained in this object.
     */
    public BigInteger getBigInt() {
        return this.bigInt;
    }

    /**
     * Create the BigIntImmutable defined by the parameter, but take care
     * of cached values.
     * @param bigIntParam The BigInteger that should be used to create the new
     * object.
     * @return A BigIntImmutable object corresponding to the given BigInteger.
     */
    public static synchronized BigIntImmutable create(final BigInteger bigIntParam) {
        BigIntImmutable result = BigIntImmutable.cache.get(bigIntParam);
        if (result == null) {
            result = new BigIntImmutable(bigIntParam);
            BigIntImmutable.cache.put(bigIntParam, result);
        }
        return result;
    }

    /**
     * @return the string representation of the BigInteger object.
     */
    @Override
    public String toString() {
        return this.bigInt.toString();
    }

    @Override
    public String toSMTLIB() {
        if (this.bigInt.signum() == -1) {
            final StringBuilder s = new StringBuilder();
            s.append("(- ");
            s.append(this.bigInt.abs().toString());
            s.append(")");
            return s.toString();
        } else {
            return this.bigInt.toString();
        }
    }

    /**
     * @return the string representation of the BigInteger object.
     * @param o the export util, not used here.
     */
    @Override
    public String export(final Export_Util o) {
        return this.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        return XMLTag.createInteger(doc, this.bigInt.intValue());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element integer = CPFTag.INTEGER.createElement(doc);
        integer.appendChild(doc.createTextNode("" + this.bigInt.intValue()));
        return integer;
    }

}
