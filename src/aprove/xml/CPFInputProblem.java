package aprove.xml;

import org.w3c.dom.*;

import aprove.verification.oldframework.Logic.*;

public interface CPFInputProblem {

    Element getCPFInput(Document doc, XMLMetaData xmlMetaData, TruthValue result);

    Element getCPFAssumption(Document doc, XMLMetaData xmlMetaData, CPFModus modus, TruthValue result);

}
