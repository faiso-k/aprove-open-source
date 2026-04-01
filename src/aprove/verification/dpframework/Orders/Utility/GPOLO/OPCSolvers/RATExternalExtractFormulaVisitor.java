/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * WARNING: Only for testing. See ExternalRatSolver.
 * @author cotto
 */
public class RATExternalExtractFormulaVisitor
    extends AbstractFormulaExtractor<PoT> {
    /**
     * This ring is used to operate on the coefficients.
     */
    private Ring<PoT> ringC;

    /**
     * This monoid is used to operate on monomials over variables.
     */
    private CMonoid<GMonomial<GPolyVar>> monoid;

    /**
     * This visitor provides flat representations for a order polynomial.
     */
    private FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar>
        flatteningVisitorOuter;

    /**
     * This visitor provides flat representations for a gpoly (coefficient).
     */

    private FlatteningVisitor<PoT, GPolyVar> flatteningVisitorInner;

    /**
     * The ranges for the variables in the original constraints.
     */
    private Map<GPolyVar, OPCRange<PoT>> ranges;

    /**
     * The smallest exponent that may be chosen for the variables.
     */
    private BigInteger expMin;

    /**
     * The greatest exponent that may be chosen for the variables.
     */
    private BigInteger expMax;

    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<PoT, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair;

    public RATExternalExtractFormulaVisitor(final Ring<PoT> ringCParam,
            final Ring<GPoly<PoT, GPolyVar>> polyRingParam,
            final CMonoid<GMonomial<GPolyVar>> monoidParam,
            final FlatteningVisitor<PoT, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar> fvOuter,
            final Map<GPolyVar, OPCRange<PoT>> rangesParam, final BigInteger min,
            final BigInteger max) {
        this.ringC = ringCParam;
        this.monoid = monoidParam;
        this.pair =
            new Pair<Semiring<GPoly<PoT, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>(
                    polyRingParam, monoidParam);
        this.flatteningVisitorInner = fvInner;
        this.flatteningVisitorOuter = fvOuter;
        this.ranges = rangesParam;
        this.expMin = min;
        this.expMax = max;
        this.encodeBooleanRanges();
    }

    private void encodeBooleanRanges() {
        if (Globals.useAssertions) {
            assert (this.expMin.signum() != 0 || this.expMax.signum() != 0);
        }
        for (Map.Entry<GPolyVar, OPCRange<PoT>> entry
                : this.ranges.entrySet()) {
            OPCRange<PoT> range = entry.getValue();
            if (range.getList().get(0).y.equals(PoT.ONE)) {
                String var = entry.getKey().getName();
                // this is a boolean variable
                Map<IndefinitePart, BigInteger> simpleMonomials =
                    new LinkedHashMap<IndefinitePart, BigInteger>();
                IndefinitePart b = IndefinitePart.create(var, 1);
                IndefinitePart bSquared = IndefinitePart.create(var, 2);
                simpleMonomials.put(b, BigInteger.valueOf(-1));
                simpleMonomials.put(bSquared, BigInteger.ONE);
                SimplePolynomial sp = SimplePolynomial.create(simpleMonomials);
                Diophantine dio = Diophantine.create(sp, ConstraintType.EQ);
                Formula<Diophantine> newFormula =
                    this.getFormulaFactory().buildTheoryAtom(dio);
                this.buildAnd(this.getFormula(), newFormula);
            }
        }
    }

    /**
     * If an atom is reached, take care of the different variable types and use
     * Absolute Positiveness to generate the resulting formula.
     * @param atom The atom.
     * @return atom.
     */
    @Override
    public OrderPolyConstraint<PoT> caseAtom(final OPCAtom<PoT> atom) {
        Set<GPolyVar> uqVars = new LinkedHashSet<GPolyVar>();
        Set<GPolyVar> eqVars = null;
        for (OPCQuantifier<PoT> elem : this.getQuantStack()) {
            if (elem instanceof OPCQuantifierE) {
                eqVars = elem.getQuantifiedVariables();
            } else if (elem instanceof OPCQuantifierA) {
                uqVars.addAll(elem.getQuantifiedVariables());
            }
        }
        if (Globals.useAssertions) {
            assert(atom.getRightPoly() == null);
            // there may not be a free variable in this atom!
            Set<GPolyVar> allVars =
                new LinkedHashSet<GPolyVar>(atom.getFreeVariables());
            if (eqVars != null) {
                allVars.removeAll(eqVars);
            }
            allVars.removeAll(uqVars);
            assert (allVars.isEmpty());
        }

        ConstraintType ct = atom.getConstraintType();
        aprove.verification.oldframework.Algebra.Polynomials.ConstraintType coeffCt;
        if (ct.equals(ConstraintType.EQ)) {
            coeffCt = ConstraintType.EQ;
        } else {
            coeffCt = ConstraintType.GE;
        }
        aprove.verification.oldframework.Algebra.Polynomials.ConstraintType constantCt = ct;
        OrderPoly<PoT> poly = atom.getLeftPoly();
        this.flatteningVisitorOuter.applyTo(poly);

        // there is no need to handle coefficients of variables x,y,.. if there
        // are none.
        if (uqVars.size() > 0) {
            Map<GMonomial<GPolyVar>, GPoly<PoT, GPolyVar>> map =
                poly.getMonomials(this.pair);
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<PoT, GPolyVar>> entry
                    : map.entrySet()) {
                GMonomial<GPolyVar> monomial = entry.getKey();
                GPoly<PoT, GPolyVar> coeffPoly = entry.getValue();
                for (GPolyVar var : uqVars) {
                    if (monomial.getExponents().containsKey(var)) {
                        this.flatteningVisitorInner.applyTo(coeffPoly);
                        Map<GMonomial<GPolyVar>, PoT> coeffMap =
                            coeffPoly.getMonomials(this.ringC, this.monoid);
                        this.buildAnd(this.getFormula(),
                                 this.createFormula(coeffMap, coeffCt));
                    }
                }
            }
        }

        // handle the constant part
        GPoly<PoT, GPolyVar> constant = poly.getConstantPart(this.pair);
        this.flatteningVisitorInner.applyTo(constant);
        this.buildAnd(this.getFormula(), this.createFormula(constant.getMonomials(
                    this.ringC, this.monoid), constantCt));
        return atom;
    }

    private Formula<Diophantine> createFormula(
            final Map<GMonomial<GPolyVar>, PoT> map, final ConstraintType ct) {
        Map<IndefinitePart, BigInteger> monomials =
            new LinkedHashMap<IndefinitePart, BigInteger>(map.size());
        for (Map.Entry<GMonomial<GPolyVar>, PoT> entry : map.entrySet()) {
            PoT value = entry.getValue();
            if (Globals.useAssertions) {
                assert (value.getDenominator().equals(BigInteger.ONE));
            }
            BigInteger newValue = value.getNumerator();
            Map<GPolyVar, BigInteger> mon = entry.getKey().getExponents();
            Map<String, Integer> oldMon =
                new LinkedHashMap<String, Integer>(mon.size());
            for (Map.Entry<GPolyVar, BigInteger> innerEntry : mon.entrySet()) {
                oldMon.put(innerEntry.getKey().toString(),
                        innerEntry.getValue().intValue());
            }
            IndefinitePart ip = IndefinitePart.create(oldMon);
            if (!newValue.equals(BigInteger.ZERO)) {
                monomials.put(ip, newValue);
            }
        }
        SimplePolynomial sp = SimplePolynomial.create(monomials);
        Diophantine dio = Diophantine.create(sp, ct);
        return this.getFormulaFactory().buildTheoryAtom(dio);
    }
}
