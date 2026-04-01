/**
 *
 * @author noschins    ki
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions.Domains;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import immutables.*;



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
public class IntegerDomain<C extends IntRing<C>> extends SemiRingDomain<C> {

    /**
     * @param bits 0 iff Z, bit with otherwise
     */
    public static String generateSuffix(final int bits) {
        if (bits > 0) {
            return "int_" + bits;
        } else if (bits == 0) {
            return "int";
        } else {
            throw new IllegalArgumentException("bits must be >= 0");
        }
    }


    public static int decodeSuffix(final String suffix) {
        if (suffix.equals("int")) {
            return 0;
        } else if (suffix.startsWith("int_")) {
            try {
                return Integer.parseInt(suffix.substring(4));
            } catch (final Exception e) {
            }
        }
        throw new IllegalArgumentException("no integer domain");
    }


    private final C intRing;

    IntegerDomain(final C ring, final C min, final C max) {
        super(ring, min, max);
        this.intRing = ring;
    }

    @Override
    public boolean isSpecialization(final Domain dom) {
        return this.equals(dom);
    }

    @Override
    public ImmutableSet<SemiRingDomain<?>> getSpecializations() {
        return ImmutableCreator.create(Collections.<SemiRingDomain<?>>singleton(this));
    }

    @Override
    public Domain getGeneralization(final Domain otherDom) {
        if (this.equals(otherDom)) {
            return this;
        } else {
            return DomainFactory.UNKNOWN;
        }
    }

    public int getBits() {
        return this.intRing.getBits();
    }


    public C unsign(final C value) {
        return value.unsign();
    }


    @Override
    public boolean isIntegerDomain() {
        return true;
    }

    @Override
    public boolean isBooleanDomain() {
        return false;
    }

    @Override
    public boolean isBooleanRange() {
        return this.min != null && this.max != null && this.min.isZero() && this.max.isOne();
    }

    @Override
    public boolean isUserDefinedDomain() {
        return false;
    }

    @Override
    protected SemiRingDomain<C> newInstance(final C ring, final C min, final C max) {
        return ring.createVarRange(min, max);
    }

    /**
     * @return Pos, StrictPos, Neg, StrictNeg or Unknown
     */
    @Override
    public Signum getSignum() {
        Signum signum = Signum.Unknown;

        if (this.min != null) {
            final Integer minSignum = this.min.signum();
            if (minSignum > 0) {
                signum = Signum.StrictPos;
            } else if (minSignum == 0) {
                signum = Signum.Pos;
            }
        }

        if (this.max != null) {
            final Integer maxSignum = this.max.signum();
            if (maxSignum < 0) {
                signum = signum.moreSpecific(Signum.StrictNeg);
            } else if (maxSignum == 0) {
                signum = signum.moreSpecific(Signum.Neg);
            }
        }

        return signum;
    }

    @Override
    public SemiRingDomain<C> modifyRange(final C min, final C max) {
        return this.ring.createVarRange(min, max);
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