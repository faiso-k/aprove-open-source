package aprove.xml;

import org.w3c.dom.*;

public interface XMLObligationExportable extends XMLExportable {

    Element toDOM(Document doc, XMLMetaData xmlMetaData);

}
