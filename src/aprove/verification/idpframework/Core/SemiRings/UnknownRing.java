package aprove.verification.idpframework.Core.SemiRings;


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
public class UnknownRing extends IDPExportable.IDPExportableSkeleton implements UserDefinedRing<UnknownRing> {

    public static final UnknownRing INNSTANCE = new UnknownRing();

    private UnknownRing() {

    }

    @Override
    public Integer semiCompareTo(final UnknownRing other) {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing add(final UnknownRing value) {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing negate() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing subtract(final UnknownRing value) {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing mult(final UnknownRing value) {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing zero() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing one() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public boolean isZero() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public boolean isOne() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public UnknownRing getValue() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public Integer signum() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public boolean isSameRing(final SemiRing<?> other) {
        return other == this;
    }

    @Override
    public boolean isBoundedRing() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public String getDomainSuffix() {
        return "UNKNOWN";
    }

    @Override
    public SemiRingDomain<UnknownRing> createVarRange(final UnknownRing min,
        final UnknownRing max) {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public SemiRingDomain<UnknownRing> createUnknownVarRange() {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public ITerm<UnknownRing> getTerm(final IDPPredefinedMap predefinedMap) {
        throw new UnsupportedOperationException("unknown ring");
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append("UNKNONW");
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
