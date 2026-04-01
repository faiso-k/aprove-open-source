package aprove.prooftree.Export.Utility;

import java.util.*;

public class XmlContentsEntry  {
    private String name;
    private Map<String, String> attribs;
    private XmlExportable obj;

    public XmlContentsEntry(String name, XmlExportable obj) {
        this.name = name;
        this.obj  = obj;
        this.attribs = null;
    }

    public XmlContentsEntry(String name, Map<String, String> attribs, XmlExportable obj) {
        this.name = name;
        this.obj  = obj;
        this.attribs = attribs;
    }

    public String getName() {
        return new String(this.name);
    }

    public XmlExportable getExportable() {
        return this.obj;
    }

    public Map<String, String> getAttribs() {
        return this.attribs;
    }
}
