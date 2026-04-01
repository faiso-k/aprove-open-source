package aprove.xml;

import org.w3c.dom.*;

import aprove.verification.oldframework.CPF.*;

public interface CPFObligationNode {

    /**
     * exports a proof to CPF
     * @param doc
     * @param mode if true, then the positive property is shown, if false, then we have a disproof
     * @param metaData auxiliary data to store symbol-mappings, etc
     * @param statistics
     * @return
     */
    Element toCPF(Document doc, boolean mode, XMLMetaData metaData, CPFExportStatistic statistics);

}
