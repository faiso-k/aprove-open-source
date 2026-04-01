package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

public class ItpfNegationWrapper implements Immutable, XmlExportable {

    private final ItpfAtom atom;

    public ItpfNegationWrapper(ItpfAtom atom) {
        this.atom = atom;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        return new XmlContentsMap(this.atom);
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

}
