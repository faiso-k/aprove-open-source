package aprove.prooftree.Export.Utility;

import java.util.*;

/**
 * Makes an object exportable to XML format.
 * @author Tim Rohlfs
 */
public interface XmlExportable {
    public Map<String, String> getXmlAttribs(XmlExporter xe);
    public XmlContentsMap getXmlContents(XmlExporter xe);
}
