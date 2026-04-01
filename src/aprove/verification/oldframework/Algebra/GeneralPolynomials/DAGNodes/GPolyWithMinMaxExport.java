/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.xml.*;

public class GPolyWithMinMaxExport<C extends GPolyCoeff> implements Exportable, XMLObligationExportable {

    private final MaxMinToVarVisitor<C> maxMinVarVisitor;
    private final FlatteningVisitor<C, GPolyVar> fvInner;
    private final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

    private OrderPoly<C> result;

    public GPolyWithMinMaxExport(final FlatteningVisitor <C, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
            final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory) {
        this.fvInner = fvInner;
        this.fvOuter = fvOuter;
        this.maxMinVarVisitor = new MaxMinToVarVisitor<C>(fvInner, fvOuter, factory);
    }

    public void applyTo(final GPoly<GPoly<C, GPolyVar>, GPolyVar> visitable) {
        this.result = new OrderPoly<C>(this.maxMinVarVisitor.applyTo(visitable));
    }

    @Override
    public String export(final Export_Util o) {
        if (this.result == null) {
            throw new IllegalStateException("call applyTo first");
        }
        return this.result.exportFlatDeep(this.fvInner, this.fvOuter, o);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        if (this.result == null) {
            throw new IllegalStateException("call applyTo first");
        }
        return this.result.toDOM(doc, xmlMetaData, this.fvInner.getRingC());
    }

}
