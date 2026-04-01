package aprove.prooftree.Export.Utility;

import java.util.*;

public class XmlContentsMap extends LinkedHashSet<XmlContentsEntry> {
    private static final long serialVersionUID = 3651513345438091159L;

    public XmlContentsMap() {
        // intentionally left blank
    }

    public XmlContentsMap(XmlExportable obj) {
        this.add(obj);
    }

    public void add(String name, XmlExportable obj) {
        this.add(new XmlContentsEntry(name, obj));
    }

    public void add(String name, String attrib, String value, XmlExportable obj) {
        Map<String, String> attribs = new HashMap<String, String>();
        attribs.put(attrib, value);
        this.add(new XmlContentsEntry(name, attribs, obj));
    }

    public void add(String name, Map<String, String> attribs, XmlExportable obj) {
        this.add(new XmlContentsEntry(name, attribs, obj));
    }

    public void add(XmlExportable obj) {
        this.add(new XmlContentsEntry("", obj));
    }
}
