package aprove.verification.idpframework.Core.SemiRings;


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
 * @author MP
 */
public class BooleanRing extends IDPExportable.IDPExportableSkeleton
    implements
        SemiRing<BooleanRing>,
 XMLObligationExportable

{

    public static BooleanRing valueOf(final boolean value) {
        return value ? BooleanRing.TRUE : BooleanRing.FALSE;
    }

    public static final BooleanRing TRUE = new BooleanRing(true);
    public static final BooleanRing FALSE = new BooleanRing(false);

    private final boolean value;

    private BooleanRing(final boolean value) {
        this.value = value;
    }

    @Override
    public Integer semiCompareTo(final BooleanRing other) {
        if (this.value == other.value) {
            return 0;
        } else {
            return this.value ? 1 : -1;
        }
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        if (this.value) {
            sb.append("TRUE");
        } else {
            sb.append("FALSE");
        }
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("value", this.value ? "TRUE" : "FALSE");
        return m;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        return XMLTag.createBoolean(doc, this.value);
    }

    @Override
    public BooleanRing add(final BooleanRing value) {
        return BooleanRing.valueOf(this.value ^ value.value);
    }

    @Override
    public BooleanRing negate() {
        return BooleanRing.valueOf(!this.value);
    }

    @Override
    public BooleanRing subtract(final BooleanRing value) {
        return BooleanRing.valueOf(this.value ^ value.value);
    }

    @Override
    public BooleanRing mult(final BooleanRing value) {
        return BooleanRing.valueOf(this.value && value.value);
    }

    @Override
    public BooleanRing zero() {
        return BooleanRing.FALSE;
    }

    @Override
    public BooleanRing one() {
        return BooleanRing.TRUE;
    }

    @Override
    public boolean isZero() {
        return !this.value;
    }

    @Override
    public boolean isOne() {
        return this.value;
    }

    @Override
    public BooleanRing getValue() {
        return this;
    }

    @Override
    public Integer signum() {
        return 0;
    }

    @Override
    public boolean isSameRing(final SemiRing<?> other) {
        return other instanceof BooleanRing;
    }

    @Override
    public String getDomainSuffix() {
        return "bool";
    }

    @Override
    public SemiRingDomain<BooleanRing> createVarRange(final BooleanRing min,
        final BooleanRing max) {
        throw new UnsupportedOperationException("boolean ring");
    }

    @Override
    public SemiRingDomain<BooleanRing> createUnknownVarRange() {
        throw new UnsupportedOperationException("boolean ring");
    }

    @Override
    public ITerm<BooleanRing> getTerm(final IDPPredefinedMap predefinedMap) {
        return predefinedMap.getBoolean(this.value).getTerm();
    }

    @Override
    public boolean isBoundedRing() {
        return true;
    }

}
