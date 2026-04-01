package aprove.xml;

import org.w3c.dom.*;

public interface XMLProofExportable extends XMLExportable {

    Element toDOM(Document doc, XMLMetaData xmlMetaData);
    XMLMetaData adaptMetaData(XMLMetaData xmlMetaData);

}
