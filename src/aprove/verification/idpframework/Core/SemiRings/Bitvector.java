package aprove.verification.idpframework.Core.SemiRings;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public class Bitvector extends IDPExportable.IDPExportableSkeleton implements IntRing<Bitvector> {

    private final int bits;

    /**
     * Cached value: 2^(bits-1)
     */
    private final BigInteger twoToKm1;

    /**
     * Cached value: 2^bits
     */
    private final BigInteger twoToK;

    public Bitvector(final int bits) {
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
    public int getBits() {
        return this.bits;
    }

    @Override
    public Bitvector add(final Bitvector value) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getDomainSuffix() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector getValue() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean isOne() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isSameRing(final SemiRing<?> other) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isZero() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public Bitvector mult(final Bitvector value) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector negate() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector one() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Integer signum() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector subtract(final Bitvector value) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector zero() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Integer semiCompareTo(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector sign() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector unsign() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public SemiRingDomain<Bitvector> createVarRange(final Bitvector min, final Bitvector max) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public SemiRingDomain<Bitvector> createUnknownVarRange() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ITerm<Bitvector> getTerm(final IDPPredefinedMap predefinedMap) {
        return null;
    }

    @Override
    public Bitvector div(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector mod(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector bitwiseAnd(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector bitwiseOr(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector bitwiseXor(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Bitvector bitwiseNot() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean isBoundedRing() {
        return true;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        // TODO Auto-generated method stub

    }

    @Override
    public Bitvector gcd(final Bitvector other) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

}
