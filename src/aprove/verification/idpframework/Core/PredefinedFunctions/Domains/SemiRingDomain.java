package aprove.verification.idpframework.Core.PredefinedFunctions.Domains;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public abstract class SemiRingDomain<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements Domain, BooleanPolyVarKeyable, XmlExportable {

    protected final C max;
    protected final C min;
    protected final C ring;
    private int hashCode;

    protected SemiRingDomain(final C ring, final C min, final C max) {
        this.ring = ring;
        this.min = min;
        this.max = max;
        final int prime = 31;
        {
            int result = 1;
            result = prime * result + ((max == null) ? 0 : max.hashCode());
            result = prime * result + ((min == null) ? 0 : min.hashCode());
            result = prime * result + ((ring == null) ? 0 : ring.hashCode());
            this.hashCode = result;
        }
    }

    public C getMax() {
        return this.max;
    }

    public C getMin() {
        return this.min;
    }

    @Override
    public boolean isSemiRingDomain() {
        return true;
    }

    public abstract boolean isBooleanRange();

    @Override
    public String getBooleanPolyVarName() {
        return this.getSuffix();
    }

    @Override
    public String getSuffix() {
        return this.ring.getDomainSuffix();
    }

    public Signum getSignum() {
        return null;
    }

    public C getRing() {
        return this.ring;
    }

    public boolean isBoolRange() {
        return this.min != null && this.min.isZero() && this.max != null && this.max.isOne();
    }

    public boolean hasBounds() {
        return this.min != null || this.max != null;
    }

    public boolean inRange(final SemiRing<?> val) {
        if (this.ring.isSameRing(val)) {
            final C ringVal = (C) val;
            return (this.min == null || ringVal.semiCompareTo(this.min) >= 0) &&
            (this.max == null || ringVal.semiCompareTo(this.max) <= 0);
        } else {
            return false;
        }
    }

    @Override
    public Domain getGeneralization(final Domain otherDom) {
        if (otherDom.isSemiRingDomain()) {
            try {
                final SemiRingDomain<C> other = (SemiRingDomain<C>) otherDom;
                if (other.getRing().isSameRing(this.ring)) {

                    final Integer minCompare = other.min.semiCompareTo(other.min);
                    final Integer maxCompare = other.max.semiCompareTo(other.max);
                    if (minCompare == null || maxCompare == null) {
                        throw new UnsupportedOperationException(
                            "min / max not comparable");
                    }

                    return this.newInstance(this.ring, minCompare > 0 ? this.min : other.min,
                        maxCompare > 0 ? other.max : this.max);
                }
            } catch (final ClassCastException e) {
                throw new UnsupportedOperationException("incompatible domains");
            }
        }
        return DomainFactory.UNKNOWN;
    }

    public abstract SemiRingDomain<C> modifyRange(C min, C max);

    protected abstract SemiRingDomain<C> newInstance(final C ring2, final C c, final C c2);

    @Override
    public boolean isSpecialization(final Domain dom) {
        return this.getSpecializations().contains(dom);
    }

    public abstract ImmutableSet<SemiRingDomain<?>> getSpecializations();

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(this.ring.getDomainSuffix());
        if (this.hasBounds()) {
            sb.append(o.escape("["));
            if (this.min != null) {
                sb.append(this.min.export(o));
            } else {
                sb.append(o.jokerSign());
            }
            sb.append(", ");
            if (this.max != null) {
                sb.append(this.max.export(o));
            } else {
                sb.append(o.jokerSign());
            }
            sb.append(o.escape("]"));
        }
    }

    public Map<String, String> getXmlAttrib() {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("domainSuffix", this.ring.getDomainSuffix());
        return m;
    }

    public Vector<XmlExportable> getContents() {
        return null;
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
        final SemiRingDomain<?> other = (SemiRingDomain<?>) obj;
        if (!this.ring.equals(other.ring)) {
            return false;
        }
         if (this.max == null) {
            if (other.max != null) {
                return false;
            }
        } else if (!this.max.equals(other.max)) {
            return false;
        }
        if (this.min == null) {
            if (other.min != null) {
                return false;
            }
        } else if (!this.min.equals(other.min)) {
            return false;
        }
        return true;
    }


}