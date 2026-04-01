package aprove.verification.dpframework.Orders ;

import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;


/**
 *   Interface for orders between Ts.
 */
public interface ExportableOrder<T> extends Order<T>, Exportable, CPFAdditional {

    /**
     * returns null, if the order is supported, and a description of the order otherwise
     */
    String isCPFSupported();
}
