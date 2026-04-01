/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

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
    public String export(Export_Util o) {
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

}
