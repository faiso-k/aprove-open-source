package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Produces a nice (flat) string representation of an OrderPolyConstraint,
 * according to a PolyFormatter.
 *
 * Expects the OPC to have the form E(...){AND{atom, atom, ...}}.
 * The polynomials in the atom should be over the inner ring only,
 * that is, we should be able to call OrderPoly.getInnerPoly().
 */
public class OPCStringifier<C extends GPolyCoeff> {

    public static <C extends GPolyCoeff> String OPCtoString(
            OrderPolyConstraint<C> constraints, PolyFormatter format,
            FlatteningVisitor<C, GPolyVar> fvInner) {
        return new OPCStringifier<C>(constraints, format, fvInner).makeString();
    }

    // Everything from here on is private, as this is really just one huge
    // static method, broken up into fields and methods to increase readability.
    private final StringBuilder buf = new StringBuilder();
    private final PolyFormatter format;
    private final OrderPolyConstraint<C> constraintsRoot;
    private final FlatteningVisitor<C,GPolyVar> fvInner;

    private OPCStringifier(OrderPolyConstraint<C> constraints, PolyFormatter format,
            FlatteningVisitor<C,GPolyVar> fvInner) {
        this.constraintsRoot = constraints;
        this.format = format;
        this.fvInner = fvInner;
    }

    private String makeString() {
        if (! (this.constraintsRoot instanceof OPCQuantifierE)) {
            throw new IllegalArgumentException("External OPC solver needs formula like E(AND(constraints))");
        }
        OPCQuantifierE<C> quantifier = (OPCQuantifierE<C>) this.constraintsRoot;
        OrderPolyConstraint<C> inner = quantifier.getInnerConstraint();
        if (! (inner instanceof OPCAnd)) {
            throw new IllegalArgumentException("External OPC solver needs formula like E(AND(constraints))");
        }
        OPCAnd<C> andNode = (OPCAnd<C>) inner;
        for (OrderPolyConstraint<C> atom: andNode.getOperands()) {
            this.appendAtom(atom);
            this.buf.append(";\n");
        }
        // Cut off the last ";\n" as multisolver format does not like it
        return this.buf.substring(0, this.buf.length()-2);
    }

    private void appendAtom(OrderPolyConstraint<C> constraint) {
        if (!(constraint instanceof OPCAtom)) {
            throw new IllegalArgumentException("Non-atom encountered inside AND");
        }
        OPCAtom<C> atom = (OPCAtom<C>) constraint;
        this.appendOrderPoly(atom.getLeftPoly());
        this.buf.append(atom.getConstraintType());
        this.appendOrderPoly(atom.getRightPoly());
    }

    private void appendOrderPoly(OrderPoly<C> orderPolyOrNull) {
        if (orderPolyOrNull == null) {
            this.buf.append("0");
            return;
        }
        GPoly<C, GPolyVar> poly = orderPolyOrNull.getInnerPoly();

        this.fvInner.applyTo(poly);
        Semiring<C> ring = this.fvInner.getRingC();
        Map<GMonomial<GPolyVar>, C> map =
            poly.getMonomials(ring, this.fvInner.getMonoid());
        boolean first = true;
        for (Map.Entry<GMonomial<GPolyVar>, C> entry : map.entrySet()) {
            GMonomial<GPolyVar> monomial = entry.getKey();
            C coeff = entry.getValue();
            if (coeff.equals(ring.zero())) {
                continue;
            }

            if (!first) {
                this.buf.append(" + ");
            }
            first = false;

            Map<GPolyVar, BigInteger> exponents = monomial.getExponents();
            if (exponents.isEmpty()) {
                this.buf.append(coeff.toString());
            } else {
                if (! coeff.equals(ring.one())) {
                    this.buf.append(coeff.toString());
                    this.buf.append(this.format.getMult());
                }
                this.appendMonomial(exponents);
            }
        }
        // If we never wrote anything...
        if (first) {
            this.buf.append("0");
        }
    }

    private void appendMonomial(Map<GPolyVar, BigInteger> exponents) {
        boolean first = true;
        for(Map.Entry<GPolyVar, BigInteger> entry: exponents.entrySet()) {
            GPolyVar var = entry.getKey();
            BigInteger exponent = entry.getValue();
            if (! first) {
                this.buf.append(this.format.getMult());
            }
            first = false;
            this.buf.append(this.format.mapVar(var.getName()));
            if (! exponent.equals(BigInteger.ONE)) {
                if (this.format.getExp() != null) {
                    this.buf.append(this.format.getExp());
                    this.buf.append(exponent);
                } else {
                    for(int i=1; i<exponent.intValue(); i++) {
                        this.buf.append(this.format.getMult());
                        this.buf.append(this.format.mapVar(var.getName()));
                    }
                }
            }
        }
        if (first) { // Shouldn't happen, but this would be the right answer
            this.buf.append("1");
        }
    }
}
