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
 * @author Martin Pluecker
 */
public final class UnknownDomain extends SemiRingDomain<UnknownRing> {

    public static String SUFFIX = "Unknown";

    protected static UnknownDomain createNew() {
        return new UnknownDomain();
    }

    private UnknownDomain() {
        super(UnknownRing.INNSTANCE, null, null);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(UnknownDomain.SUFFIX);
    }

    @Override
    public boolean isSpecialization(final Domain dom) {
        throw new UnsupportedOperationException("UnknownDomain is not comparable");
    }

    @Override
    public ImmutableSet<SemiRingDomain<?>> getSpecializations() {
        throw new UnsupportedOperationException("all domains are specializations");
    }

    @Override
    public Domain getGeneralization(final Domain otherDom) {
        return this;
    }

    @Override
    public String getSuffix() {
        return UnknownDomain.SUFFIX;
    }

    @Override
    public boolean isBooleanDomain() {
        return false;
    }

    @Override
    public boolean isUserDefinedDomain() {
        return false;
    }

    @Override
    public boolean isSemiRingDomain() {
        return false;
    }

    @Override
    public boolean isIntegerDomain() {
        return false;
    }

    @Override
    public boolean isBooleanRange() {
        return false;
    }

    @Override
    public SemiRingDomain<UnknownRing> modifyRange(final UnknownRing min,
        final UnknownRing max) {
        throw new UnsupportedOperationException("range not allowed for UnknownDomain");
    }

    @Override
    protected SemiRingDomain<UnknownRing> newInstance(final UnknownRing ring,
        final UnknownRing min,
        final UnknownRing max) {
        throw new UnsupportedOperationException("UnknownDomain is singleton");
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

}
