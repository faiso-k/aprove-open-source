/**
 *
 * @author noschins    ki
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions.Domains;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;
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

public final class BooleanDomain extends SemiRingDomain<BooleanRing> {

    public static String SUFFIX = "Booleans";

    protected static final BooleanDomain BOOLEAN = new BooleanDomain();

    private BooleanDomain() {
        super(BooleanRing.TRUE, null, null);
    }

    @Override
    public boolean isUserDefinedDomain() {
        return false;
    }

    @Override
    public boolean isBooleanDomain() {
        return true;
    }


    @Override
    public boolean isSemiRingDomain() {
        return false;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append("Boolean");
    }

    @Override
    public ImmutableSet<SemiRingDomain<?>> getSpecializations() {
        return ImmutableCreator.create(Collections.<SemiRingDomain<?>>singleton(this));
    }

    @Override
    public boolean isSpecialization(final Domain dom) {
        return this.equals(dom);
    }

    @Override
    public Domain getGeneralization(final Domain otherDom) {
        if (this.equals(otherDom)) {
            return this;
        } else {
            return DomainFactory.UNKNOWN;
        }
    }

    @Override
    public String getSuffix() {
        return BooleanDomain.SUFFIX;
    }

    @Override
    public boolean isBooleanRange() {
        return true;
    }

    @Override
    public boolean isIntegerDomain() {
        return false;
    }

    @Override
    public SemiRingDomain<BooleanRing> modifyRange(final BooleanRing min,
        final BooleanRing max) {
        throw new UnsupportedOperationException("boolean domain");
    }

    @Override
    protected SemiRingDomain<BooleanRing> newInstance(final BooleanRing ring2,
        final BooleanRing c,
        final BooleanRing c2) {
        throw new UnsupportedOperationException("boolean domain");
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("value", "Boolean");
        return m;
    }

}
