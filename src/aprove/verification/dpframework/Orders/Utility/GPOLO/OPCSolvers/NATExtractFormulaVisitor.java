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
 * An ExtractFormulaVisitor can be used to convert the given OrderPolyConstraint
 * to some diophantine constraints using Absolute Positiveness.
 * @author cotto
 */
public class NATExtractFormulaVisitor
    extends AbstractFormulaExtractor<BigIntImmutable> {
    /**
     * This ring is used to operate on the coefficients.
     */
    private Ring<BigIntImmutable> ringC;

    /**
     * This monoid is used to operate on monomials over variables.
     */
    private CMonoid<GMonomial<GPolyVar>> monoid;

    /**
     * This visitor provides flat representations for a order polynomial.
     */
    private FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>
        flatteningVisitorOuter;

    /**
     * This visitor provides flat representations for a gpoly (coefficient).
     */

    private FlatteningVisitor<BigIntImmutable, GPolyVar> flatteningVisitorInner;

    /**
     * The ranges for the variables.
     */
    private Map<GPolyVar, OPCRange<BigIntImmutable>> ranges;

    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<BigIntImmutable, GPolyVar>>,
        CMonoid<GMonomial<GPolyVar>>> pair;

    /**
     * Create a new ExtractSPCsVisitor.
     * @param ringCParam A ring over C (which is BigIntImmutable here).
     * @param polyRingParam A ring over polynomials.
     * @param monoidParam A monoid over monomials over variables.
     * @param fvInner A flattening visitor for coefficient polynomials.
     * @param fvOuter A flattening visitor for order polynomials.
     * @param rangesParam The ranges for the variables.
     */
    public NATExtractFormulaVisitor(
            final Ring<BigIntImmutable> ringCParam,
            final Ring<GPoly<BigIntImmutable, GPolyVar>> polyRingParam,
            final CMonoid<GMonomial<GPolyVar>> monoidParam,
            final FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>
                fvOuter,
            final Map<GPolyVar, OPCRange<BigIntImmutable>> rangesParam) {
        this.ringC = ringCParam;
        this.monoid = monoidParam;
        this.pair =
            new Pair<Semiring<GPoly<BigIntImmutable, GPolyVar>>,
            CMonoid<GMonomial<GPolyVar>>>(polyRingParam, monoidParam);
        this.flatteningVisitorInner = fvInner;
        this.flatteningVisitorOuter = fvOuter;
        this.ranges = rangesParam;
    }

    /**
     * Transform the ranges map.
     * @return The ranges as a map String to Integer.
     */
    public Map<String, BigInteger> getRanges() {
        Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>();
        for (Map.Entry<GPolyVar, OPCRange<BigIntImmutable>> entry
                : this.ranges.entrySet()) {
            List<Pair<BigIntImmutable, BigIntImmutable>> list =
                entry.getValue().getList();
            if (Globals.useAssertions) {
                assert (list != null && list.size() == 1);
            }
            // yeah.
            BigInteger integer = list.iterator().next().y.getBigInt();
            result.put(entry.getKey().getName(), integer);
        }
        return result;
    }

    /**
     * If an atom is reached, take care of the different variable types and
     * use Absolute Positiveness to generate the resulting SPCs.
     * @param atom The atom.
     */
    @Override
    public void fcaseAtom(
            final OPCAtom<BigIntImmutable> atom) {
        Set<GPolyVar> uqVars = new LinkedHashSet<GPolyVar>();
        Set<GPolyVar> eqVars = null;
        for (OPCQuantifier<BigIntImmutable> elem : this.getQuantStack()) {
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
        OrderPoly<BigIntImmutable> poly = atom.getLeftPoly();
        this.flatteningVisitorOuter.applyTo(poly);
        Map<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> map =
            poly.getMonomials(this.flatteningVisitorOuter.getRingC(),
                    this.flatteningVisitorOuter.getMonoid());

        for (Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>>
                entry : map.entrySet()) {
            GMonomial<GPolyVar> monomial = entry.getKey();
            GPoly<BigIntImmutable, GPolyVar> coeffPoly = entry.getValue();
            for (GPolyVar var : uqVars) {
                if (monomial.getExponents().containsKey(var)) {
                    BigInteger exponent = monomial.getExponents().get(var);
                    // there might be exponents which are 0.
                    if (exponent.signum() == 1) {
                        this.flatteningVisitorInner.applyTo(coeffPoly);
                        Map<GMonomial<GPolyVar>, BigIntImmutable> coeffMap =
                            coeffPoly.getMonomials(this.ringC, this.monoid);
                        SimplePolynomial sp = this.createSP(coeffMap);
                        Diophantine dio = Diophantine.create(sp, coeffCt);
                        Formula<Diophantine> newFormula =
                            this.getFormulaFactory().buildTheoryAtom(dio);
                        this.buildAnd(this.getFormula(), newFormula);
                    }
                }
            }
        }
        GPoly<BigIntImmutable, GPolyVar> constant =
            poly.getConstantPart(this.pair);
        this.flatteningVisitorInner.applyTo(constant);
        SimplePolynomial constantSP =
            this.createSP(constant.getMonomials(this.ringC, this.monoid));
        Diophantine dio = Diophantine.create(constantSP, constantCt);
        Formula<Diophantine> newFormula =
            this.getFormulaFactory().buildTheoryAtom(dio);
        this.buildAnd(this.getFormula(), newFormula);
    }

    /**
     * Create a SimplePolynomial out of the given map.
     * @param map Each monomial has a coefficient.
     * @return A SimplePoly which represents the polynomial given in the map.
     */
    private SimplePolynomial createSP(
            final Map<GMonomial<GPolyVar>, BigIntImmutable> map) {
        Map<IndefinitePart, BigInteger> newMap =
            new LinkedHashMap<IndefinitePart, BigInteger>(map.size());
        for (Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> entry
                : map.entrySet()) {
            Map<GPolyVar, BigInteger> mon = entry.getKey().getExponents();
            Map<String, Integer> oldMon =
                new LinkedHashMap<String, Integer>(mon.size());
            for (Map.Entry<GPolyVar, BigInteger> innerEntry : mon.entrySet()) {
                oldMon.put(innerEntry.getKey().toString(),
                        innerEntry.getValue().intValue());
            }
            IndefinitePart ip = IndefinitePart.create(oldMon);
            BigInteger bigInt = entry.getValue().getBigInt();
            if (bigInt.signum() != 0) {
                newMap.put(ip, bigInt);
            }
        }
        return SimplePolynomial.create(newMap);
    }
}
