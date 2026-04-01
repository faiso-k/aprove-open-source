package aprove.verification.idpframework.Core.PredefinedFunctions.Domains;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class UserDefinedDomain extends SemiRingDomain<UnknownRing> {

    private final int id;
    private final ImmutableSet<SemiRingDomain<?>> specializations;
    private final ImmutableSet<SemiRingDomain<?>> extendedSpecializations;
    private final int hashCode;

    UserDefinedDomain(final int id, final ImmutableSet<SemiRingDomain<?>> specializations) {
        super(UnknownRing.INNSTANCE, null, null);
        this.id = id;
        this.specializations = specializations;

        this.hashCode = id * 11 + specializations.hashCode() * 121;

        final LinkedHashSet<SemiRingDomain<?>> spec = new LinkedHashSet<SemiRingDomain<?>>(specializations);
        spec.add(this);
        this.extendedSpecializations = ImmutableCreator.create(spec);
    }

    @Override
    public boolean isUserDefinedDomain() {
        return true;
    }

    @Override
    public boolean isBooleanDomain() {
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

    public int getId() {
        return this.id;
    }

    @Override
    public ImmutableSet<SemiRingDomain<?>> getSpecializations() {
        return this.extendedSpecializations;
    }

    @Override
    public Domain getGeneralization(final Domain otherDom) {
        if (this.isSpecialization(otherDom)) {
            return this;
        } else {
            return DomainFactory.UNKNOWN;
        }
    }

    @Override
    public SemiRingDomain<UnknownRing> modifyRange(final UnknownRing min,
        final UnknownRing max) {
        throw new UnsupportedOperationException("range not allowed for UserDefinedDomain");
    }

    @Override
    protected SemiRingDomain<UnknownRing> newInstance(final UnknownRing ring,
        final UnknownRing min,
        final UnknownRing max) {
        throw new UnsupportedOperationException("UserDefinedDomain can not be modified");
    }

    @Override
    public String getSuffix() {
        return "UD_" + this.id;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append("UD_");
        sb.append(this.id);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
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
        final UserDefinedDomain other = (UserDefinedDomain) obj;
        return other.id == this.id && this.specializations.equals(other.specializations);
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

}
