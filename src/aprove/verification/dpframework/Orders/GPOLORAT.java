package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.xml.*;

/**
 * @author Carsten Otto
 * @version $Id$
 */
public class GPOLORAT extends GPOLO<PoT> {
    /**
     * This value is used to define the strict ordering.
     */
    private final PoT delta;

    /**
     * Create the order based on the given interpretation.
     * @param inter The interpretation.
     * @param orderPolyFactory a factory used to create order polynomials.
     * @param inner A FlatteningVisitor for inner polynomials.
     * @param outer A FlatteningVisitor for OrderPolys.
     * @param pairs The P rules.
     */
    public GPOLORAT(final GInterpretation<PoT> inter,
            final OrderPolyFactory<PoT> orderPolyFactory,
            final FlatteningVisitor<PoT, GPolyVar> inner,
            final FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar> outer,
            final Set<? extends GeneralizedRule> pairs) {
        super(inter, orderPolyFactory, inner, outer,
                new PoTOrder());
        this.delta = this.getDelta(pairs);
    }

    /**
     * @param pairs The P rules.
     * @return the delta value used to define the strict ordering.
     */
    private PoT getDelta(final Set<? extends GeneralizedRule> pairs) {
        final CoeffOrder<PoT> potOrder = new PoTOrder();
        final Ring<PoT> potRing = (Ring<PoT>)this.getFvInner().getRingC();
        final CMonoid<GMonomial<GPolyVar>> monoid = this.getFvInner().getMonoid();
        final Semiring<GPoly<PoT, GPolyVar>> outerRing = this.getFvOuter().getRingC();
        final GInterpretation<PoT> inter = this.getInterpretation();
        final OrderPolyFactory<PoT> factory = this.getFactory();
        PoT min = null;
        for (final GeneralizedRule pair : pairs) {
            final TRSTerm left = pair.getLhsInStandardRepresentation();
            final TRSTerm right = pair.getRhsInStandardRepresentation();
            // TODO extend method signature by proper Abortion
            OrderPoly<PoT> p1, p2, pDiff;
            try {
                final Abortion dummyAborter = AbortionFactory.create();
                p1 = inter.interpretTerm(left, dummyAborter);
                p2 = inter.interpretTerm(right, dummyAborter);
            } catch (final AbortionException e) {
                throw new RuntimeException(e);
            }
            pDiff = factory.minus(p1, p2);
            if (this.constraintFulfilled(pDiff, ConstraintType.GT)) {
                // the pair is oriented strictly, so get the implicit value of
                // delta (>= 0) for this pair
                final GPoly<PoT, GPolyVar> constant =
                    pDiff.getConstantPart(outerRing, monoid);
                final PoT coeff = constant.getConstantPart(potRing, monoid);
                if (min == null
                        || potOrder.signum(potRing.minus(min, coeff)) > 0) {
                    min = coeff;
                }
            }
        }
        if (Globals.useAssertions) {
            // min != null && min > 0
            assert (min != null) : "No pair oriented?";
            assert (min.getPair().x.signum() > 0);
        }
        return min;
    }

    /**
     * @return the representation according to the given export util.
     * @param eu the export util that should be used to create the string
     * representation.
     */
    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        sb.append(super.export(eu));
        sb.append("The value of delta used in the strict ordering is ");
        sb.append(this.delta.toString());
        sb.append(".");
        return sb.toString();
    }

    @Override
    protected Element toCPFDomain(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.RATIONALS.create(doc, CPFTag.DELTA.create(doc, this.delta.toCPF(doc, xmlMetaData)));
    }

}
