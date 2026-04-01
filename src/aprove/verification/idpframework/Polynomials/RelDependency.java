/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Polynomials;


import java.util.*;

import aprove.prooftree.Export.Utility.*;

public enum RelDependency implements Exportable, XmlExportable {

    Increasing(1), Decreasing(-1), Independent(0), Wild(2);

    private final Integer k;

    RelDependency(final Integer k) {
        this.k = k;
    }

    public Integer getK() {
        return this.k;
    }

    @Override
    public final String export(final Export_Util o) {
        return this.toString();
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        Map<String, String> m = new HashMap<String, String>();
        m.put("value", this.toString());
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        return null;
    }

    public RelDependency combine(final RelDependency other) {
        if (other == null) {
            return this;
        }

        switch (this.k * other.k) {
        case -2 :
        case 2  :
        case 4  :
            return Wild;
        case 1 :
            return Increasing;
        case -1 :
            return Decreasing;
        case 0 :
            return Independent;
        default :
            throw new UnsupportedOperationException("unknown combination");
        }
    }

}
