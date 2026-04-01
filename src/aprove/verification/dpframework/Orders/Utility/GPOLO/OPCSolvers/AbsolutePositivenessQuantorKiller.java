package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class visits OrderPolyConstraints and applies a sound transformation
 * to remove all-quantors.
 *
 * That is, the result of this visitor is a formula such that:
 *  - All solutions of the new formula solve the old formula as well
 *  - No all-quantors are contained in the formula.
 */
public class AbsolutePositivenessQuantorKiller<C extends GPolyCoeff>
        extends ConstraintVisitor.ConstraintVisitorSkeleton<C> {
    /**
     * This visitor provides flat representations for a order polynomial.
     */
    private FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar>
        flatteningVisitorOuter;

    /**
     * The E-quantifier outside where we are
     * used only for a sanity check to ensure our atoms don't have free variables
     */
    protected OPCQuantifierE<C> existenceQuantifier = null;

    /**
     * The All-quantors traversed up to where we are.
     * Used to ensure we remove the right variables.
     */
    protected Stack<OPCQuantifierA<C>> allQuantStack =
        new Stack<OPCQuantifierA<C>>();

    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<C, GPolyVar>>,
        CMonoid<GMonomial<GPolyVar>>> polyringWithMonoid;

    /**
     * As we need to create new polynomials, the thing that allows us to do so.
     */
    private GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> outerFactory =
        new FullSharingFactory<GPoly<C,GPolyVar>, GPolyVar>();


    /**
     * Create a new ExtractSPCsVisitor.
     * @param polyRingParam A ring over polynomials.
     * @param monoidParam A monoid over monomials over variables.
     * @param fvOuter A flattening visitor for order polynomials.
     */
    public AbsolutePositivenessQuantorKiller(
            final Ring<GPoly<C, GPolyVar>> polyRingParam,
            final CMonoid<GMonomial<GPolyVar>> monoidParam,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter) {
        this.polyringWithMonoid =
            new Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>(
                    polyRingParam, monoidParam);
        this.flatteningVisitorOuter = fvOuter;
    }

    @Override
    public void fcaseNot(final OPCNot<C> not) {
        throw new UnsupportedOperationException("Absolute positiveness does not support NOT");
    }

    @Override
    public void fcaseQuantifierE(OPCQuantifierE<C> quant) {
        if (this.existenceQuantifier != null) {
            throw new IllegalArgumentException("Absolute positiveness does not like nested E quantifiers");
        }
        this.existenceQuantifier = quant;
    }

    @Override
    public OrderPolyConstraint<C> caseQuantifierE(OPCQuantifierE<C> quant,
            OrderPolyConstraint<C> newConstraint) {
        if (Globals.useAssertions) {
            assert quant.equals(this.existenceQuantifier);
        }
        this.existenceQuantifier = null;
        return super.caseQuantifierE(quant, newConstraint);
    }

    @Override
    public void fcaseQuantifierA(OPCQuantifierA<C> quant) {
        this.allQuantStack.push(quant);
    }

    @Override
    public OrderPolyConstraint<C> caseQuantifierA(
            final OPCQuantifierA<C> quant,
            final OrderPolyConstraint<C> newConstraint) {
        OPCQuantifierA<C> stackSanity = this.allQuantStack.pop();
        if (Globals.useAssertions) {
            assert quant.equals(stackSanity);
            // Ensure our processing did indeed remove the need for this quantifier
            Set<GPolyVar> freeVariables = newConstraint.getFreeVariables();
            Set<GPolyVar> quantifiedVariables = quant.getQuantifiedVariables();
            assert Collections.disjoint(freeVariables, quantifiedVariables);
        }
        return newConstraint;
    }

    /**
     * If an atom is reached, take care of the different variable types and use
     * Absolute Positiveness to generate the resulting formula.
     * @param atom The atom.
     */
    @Override
    public OrderPolyConstraint<C> caseAtom(
            final OPCAtom<C> atom) {
        Set<GPolyVar> uqVars = new LinkedHashSet<GPolyVar>();
        for (OPCQuantifierA<C> elem : this.allQuantStack) {
            uqVars.addAll(elem.getQuantifiedVariables());
        }
        if (Globals.useAssertions) {
            assert(atom.getRightPoly() == null);
            // there must not be any free variables in this atom!
            Set<GPolyVar> allVars =
                new LinkedHashSet<GPolyVar>(atom.getFreeVariables());
            if (this.existenceQuantifier != null) {
                allVars.removeAll(this.existenceQuantifier.getQuantifiedVariables());
            }
            allVars.removeAll(uqVars);
            assert (allVars.isEmpty());
        }
        Set<OrderPolyConstraint<C>> localConstraints = new LinkedHashSet<OrderPolyConstraint<C>>();

        ConstraintType ct = atom.getConstraintType();
        ConstraintType coeffCt;
        if (ct.equals(ConstraintType.EQ)) {
            coeffCt = ConstraintType.EQ;
        } else {
            coeffCt = ConstraintType.GE;
        }
        ConstraintType constantCt = ct;

        OrderPoly<C> poly = atom.getLeftPoly();
        this.flatteningVisitorOuter.applyTo(poly);

        // there is no need to handle coefficients of variables x,y,.. if there
        // are none.
        if (uqVars.size() > 0) {
            Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> map =
                poly.getMonomials(this.polyringWithMonoid);
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> entry
                    : map.entrySet()) {
                GMonomial<GPolyVar> monomial = entry.getKey();
                Map<GPolyVar, BigInteger> monomAsMap = monomial.getExponents();
                GPoly<C, GPolyVar> coeffPoly = entry.getValue();

                // Now the monomial is either empty (for the constant part)
                // or it contains some of our uqVars. If it contains anything else,
                // we're in trouble.
                if (Globals.useAssertions) {
                    assert uqVars.containsAll(monomAsMap.keySet());
                }

                // Constant part handled below
                if (! monomAsMap.isEmpty()) {
                    localConstraints.add(this.polyToAtom(coeffPoly, coeffCt));
                }
            }
        }

        // handle the constant part
        GPoly<C, GPolyVar> constant = poly.getConstantPart(this.polyringWithMonoid);
        localConstraints.add(this.polyToAtom(constant, constantCt));
        return new SimpleFactory<C>().createAnd(localConstraints);
    }

    private OPCAtom<C> polyToAtom(GPoly<C, GPolyVar> poly, ConstraintType ct) {
        GPoly<GPoly<C, GPolyVar>, GPolyVar> wrappedPoly = this.outerFactory.buildFromCoeff(poly);
        OrderPoly<C> orderPoly = new OrderPoly<C>(wrappedPoly);
        return new OPCAtom<C>(orderPoly, null, ct);
    }
}
