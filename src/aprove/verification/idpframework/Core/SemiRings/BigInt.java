package aprove.verification.idpframework.Core.SemiRings;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 *
 * @author Martin Pluecker
 */
public final class BigInt extends IDPExportable.IDPExportableSkeleton implements IntRing<BigInt>, Comparable<BigInt>,
        XMLObligationExportable,
        CPFAdditional
{

    public static final BigInt ZERO = BigInt.create(BigInteger.ZERO);
    public static final BigInt ONE = BigInt.create(BigInteger.ONE);
    public static final BigInt TWO = BigInt.create(BigInteger.valueOf(2));
    public static final BigInt MINUS_ONE = BigInt.ONE.negate();

    public static BigInt create(final Long value) {
        return new BigInt(BigInteger.valueOf(value));
    }

    public static BigInt create(final BigInteger value) {
        return new BigInt(value);
    }

    private final BigInteger value;

    private BigInt(final BigInteger value) {
        this.value = value;
    }

    @Override
    public BigInt add(final BigInt value) {
        return new BigInt(this.value.add(value.value));
    }

    @Override
    public BigInt negate() {
        return new BigInt(this.value.negate());
    }

    @Override
    public BigInt mult(final BigInt value) {
        return new BigInt(this.value.multiply(value.value));
    }

    @Override
    public BigInt subtract(final BigInt value) {
        return new BigInt(this.value.subtract(value.value));
    }

    @Override
    public boolean isZero() {
        return this.value.signum() == 0;
    }

    @Override
    public boolean isOne() {
        return this.value.equals(BigInteger.ONE);
    }

    @Override
    public int hashCode() {
        return this.value.intValue();
    }

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
        final BigInt other = (BigInt) obj;
        return this.value.equals(other.value);
    }

    @Override
    public BigInt one() {
        return BigInt.ONE;
    }

    @Override
    public BigInt zero() {
        return BigInt.ZERO;
    }

    public int intValue() {
        return this.value.intValue();
    }

    public BigInteger getBigInt() {
        return this.value;
    }

    @Override
    public BigInt getValue() {
        return this;
    }

    public BigInt abs() {
        if (this.signum() < 0) {
            return this.negate();
        } else {
            return this;
        }
    }

    @Override
    public Integer signum() {
        return this.value.signum();
    }

    @Override
    public int compareTo(final BigInt o) {
        return this.value.compareTo(o.value);
    }

    @Override
    public Integer semiCompareTo(final BigInt other) {
        return this.value.compareTo(other.getValue().getBigInt());
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        return XMLTag.createInteger(doc, this.value.intValue());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element integer = CPFTag.INTEGER.createElement(doc);
        integer.appendChild(doc.createTextNode("" + this.value.intValue()));
        return integer;
    }

    public boolean isEven() {
        return this.value.and(BigInteger.ONE).signum() == 0;
    }

    @Override
    public boolean isSameRing(final SemiRing<?> other) {
        return other instanceof BigInt;
    }

    @Override
    public String getDomainSuffix() {
        return "INT";
    }

    @Override
    public int getBits() {
        return 0;
    }

    @Override
    public BigInt sign() {
        return this;
    }

    @Override
    public BigInt unsign() {
        return this;
    }

    @Override
    public SemiRingDomain<BigInt> createVarRange(final BigInt min, final BigInt max) {
        return DomainFactory.createVarRange(this, min, max);
    }

    @Override
    public SemiRingDomain<BigInt> createUnknownVarRange() {
        return DomainFactory.createUnknownVarRange(this);
    }

    @Override
    public ITerm<BigInt> getTerm(final IDPPredefinedMap predefinedMap) {
        return ITerm.createFunctionApplication(predefinedMap.getIntSym(this, DomainFactory.INTEGERS));
    }

    @Override
    public BigInt div(final BigInt other) {
        return BigInt.create(this.value.divide(other.value));
    }

    @Override
    public BigInt gcd(final BigInt other) {
        return BigInt.create(this.value.gcd(other.value));
    }

    @Override
    public BigInt mod(final BigInt other) {
        return BigInt.create(this.value.remainder(other.value));
    }

    @Override
    public BigInt bitwiseAnd(final BigInt other) {
        return BigInt.create(this.value.and(other.value));
    }

    @Override
    public BigInt bitwiseOr(final BigInt other) {
        return BigInt.create(this.value.or(other.value));
    }

    @Override
    public BigInt bitwiseXor(final BigInt other) {
        return BigInt.create(this.value.xor(other.value));
    }

    @Override
    public BigInt bitwiseNot() {
        return BigInt.create(this.value.not());
    }

    @Override
    public boolean isBoundedRing() {
        return false;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(this.value.toString());
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String>m = new HashMap<String, String>();
        m.put("value", this.value.toString());
        return m;
    }

}
