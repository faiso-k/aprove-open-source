package aprove.verification.dpframework.Orders ;

import org.w3c.dom.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;


/**
 *   Interface for orders which are exportable to CPF and may be combined with Argument filters
 */
public interface CPFExportableAfsOrder extends ExportableOrder<TRSTerm> {

    /**
     * exports this order into CPF
     * @param doc
     * @param xmlMetaData
     * @param fs the set of function symbols to be exported
     * @param afs an optional AFS that is used before the order; may be null
     * @return the CPF-Element for this order (+ Afs)
     */
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Iterable<FunctionSymbol> fs,
        final Afs afs);
}
