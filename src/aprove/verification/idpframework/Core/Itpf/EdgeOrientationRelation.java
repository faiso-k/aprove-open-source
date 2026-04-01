/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

public enum EdgeOrientationRelation implements Immutable, Exportable, XmlExportable {

    ABSTRACT_GT(false, false, true), ABSTRACT_WEAK_GT(false, false, true), ABSTRACT_GE(
            true, false, true), ABSTRACT_WEAK_BOUND(false, false, true), ABSTRACT_STRICT_BOUND(
            false, false, true), ABSTRACT_COMPLEXITY_WEAK_GT(false, false, true); // we don't really need or support that, for future use

    private final boolean isReflexive;
    private final boolean isRewriteRel;
    private final boolean isAbstract;

    private EdgeOrientationRelation(final boolean reflexive, final boolean isRewriteRel, final boolean isAbstract) {
        this.isReflexive = reflexive;
        this.isRewriteRel = isRewriteRel;
        this.isAbstract = isAbstract;
    }

    @Override
    public final String export(final Export_Util o) {
        switch (this) {
        case ABSTRACT_GE:
            return o.idpCCGE();
        case ABSTRACT_GT:
            return o.idpCCGT();
        case ABSTRACT_WEAK_GT:
            return o.idpCCWGT();
        case ABSTRACT_WEAK_BOUND:
            return o.idpCCGE();
        case ABSTRACT_STRICT_BOUND:
            return o.idpCCGT() + "_c";
        case ABSTRACT_COMPLEXITY_WEAK_GT:
            return o.idpCCWGT() + "_COMPL";
        default:
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("value", this.toString());
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    public boolean isReflexive() {
        return this.isReflexive;
    }

    public boolean isRewriteRel() {
        return this.isRewriteRel;
    }

    public boolean isAbstract() {
        return this.isAbstract;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }
}
