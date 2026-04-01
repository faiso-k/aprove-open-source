package aprove.verification.dpframework.BasicStructures;

import org.w3c.dom.*;

import aprove.xml.*;

public interface Label extends XMLObligationExportable, CPFAdditional {

    public Element toDOMLabel(Document doc, XMLMetaData xmlMetaData);

}
