package aprove.verification.dpframework.Orders;


import org.w3c.dom.*;

import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.xml.*;

/**
 * @author Carsten Otto
 * @version $Id$
 */
public class GPOLONAT extends GPOLO<BigIntImmutable> {
    /**
     * Create the order based on the given interpretation.
     * @param inter The interpretation.
     * @param orderPolyFactory a factory used to create order polynomials.
     * @param inner A FlatteningVisitor for inner polynomials.
     * @param outer A FlatteningVisitor for OrderPolys.
     */
    public GPOLONAT(final GInterpretation<BigIntImmutable> inter,
            final OrderPolyFactory<BigIntImmutable> orderPolyFactory,
            final FlatteningVisitor<BigIntImmutable, GPolyVar> inner,
            final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer) {
        super(inter, orderPolyFactory, inner, outer, new BigIntImmutableOrder());
    }

    /**
     * @return the string representation of this polynomial ordering.
     */
    // commented out -- superclass method does the same, but faster
    /*
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(super.toString());
        sb.append("");
        return sb.toString();
    }
    */

    /**
     * @return the representation according to the given export util.
     * @param eu the export util that should be used to create the string
     * representation.
     */
    // commented out -- superclass method does the same, but faster (inheritance exists for a reason)
    /*
    public String export(final Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        sb.append(super.export(eu));
        return sb.toString();
    }
    */

    @Override
    protected Element toCPFDomain(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.NATURALS.create(doc);
    }
}
