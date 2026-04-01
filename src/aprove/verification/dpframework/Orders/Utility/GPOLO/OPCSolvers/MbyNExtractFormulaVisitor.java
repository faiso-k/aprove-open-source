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
 * @author cotto
 */
public class MbyNExtractFormulaVisitor extends AbstractFormulaExtractor<MbyN> {
    /**
     * This ring is used to operate on the coefficients.
     */
    private Ring<MbyN> ringC;

    /**
     * This monoid is used to operate on monomials over variables.
     */
    private CMonoid<GMonomial<GPolyVar>> monoid;

    /**
     * This visitor provides flat representations for a order polynomial.
     */
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>
        flatteningVisitorOuter;

    /**
     * This visitor provides flat representations for a gpoly (coefficient).
     */

    private FlatteningVisitor<MbyN, GPolyVar> flatteningVisitorInner;

    /**
     * The ranges for the variables in the original constraints.
     */
    private Map<GPolyVar, OPCRange<MbyN>> ranges;

    /**
     * The ranges for the variables in the resulting simple poly constraints.
     */
    private Map<String, BigInteger> newRanges =
        new LinkedHashMap<String, BigInteger>();

    /**
     * The default range as a OPCRange.
     */
    private OPCRange<MbyN> defaultRange;

    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<MbyN, GPolyVar>>,
        CMonoid<GMonomial<GPolyVar>>> pair;

    /**
     * Remember the (SAT) variable which is the denominator for some (OPC)
     * variable.
     */
    private Map<GPolyVar, GPolyVar> denominators =
        new LinkedHashMap<GPolyVar, GPolyVar>();

    /**
     * Remember the (SAT) variable which is the numerator for some (OPC)
     * variable.
     */
    private Map<GPolyVar, GPolyVar> numerators =
        new LinkedHashMap<GPolyVar, GPolyVar>();

    /**
     * The denominator for all fractions. If null the denominators will be
     * parametric.
     */
    private BigInteger denominator;

    /**
     * Create a new ExtractSPCsVisitor.
     * @param ringCParam A ring over C (which is MbyN here).
     * @param polyRingParam A ring over polynomials.
     * @param monoidParam A monoid over monomials over variables.
     * @param fvInner A flattening visitor for coefficient polynomials.
     * @param fvOuter A flattening visitor for order polynomials.
     * @param rangesParam The ranges for the variables.
     * @param varConvParam A variable converter that can store information about
     * the connection between OPC variables and propositional variables.
     * @param defaultRangeParam The range for variables that are not mentioned
     * in rangesParam.
     * @param denominatorParam The fixed value for all denominators. This
     * overrides the ranges setting. Use "null" for denominators according to
     * the ranges.
     */
    public MbyNExtractFormulaVisitor(final Ring<MbyN> ringCParam,
            final Ring<GPoly<MbyN, GPolyVar>> polyRingParam,
            final CMonoid<GMonomial<GPolyVar>> monoidParam,
            final FlatteningVisitor<MbyN, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter,
            final Map<GPolyVar, OPCRange<MbyN>> rangesParam,
            final VariableConverterMbyN varConvParam,
            final OPCRange<MbyN> defaultRangeParam,
            final BigInteger denominatorParam) {
        this.ringC = ringCParam;
        this.monoid = monoidParam;
        this.defaultRange = defaultRangeParam;
        this.pair =
            new Pair<Semiring<GPoly<MbyN, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>(
                    polyRingParam, monoidParam);
        this.flatteningVisitorInner = fvInner;
        this.flatteningVisitorOuter = fvOuter;
        this.ranges = rangesParam;
        this.denominator = denominatorParam;
    }

    /**
     * If an atom is reached, take care of the different variable types and use
     * Absolute Positiveness to generate the resulting formula.
     * @param atom The atom.
     */
    @Override
    public void fcaseAtom(
            final OPCAtom<MbyN> atom) {
        Set<GPolyVar> uqVars = new LinkedHashSet<GPolyVar>();
        Set<GPolyVar> eqVars = null;
        for (OPCQuantifier<MbyN> elem : this.getQuantStack()) {
            if (elem instanceof OPCQuantifierE<?>) {
                eqVars = elem.getQuantifiedVariables();
            } else if (elem instanceof OPCQuantifierA<?>) {
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
        Formula<Diophantine> localConstraints =
            this.getFormulaFactory().buildConstant(true);

        ConstraintType ct = atom.getConstraintType();
        aprove.verification.oldframework.Algebra.Polynomials.ConstraintType coeffCt;
        if (ct.equals(ConstraintType.EQ)) {
            coeffCt = ConstraintType.EQ;
        } else {
            coeffCt = ConstraintType.GE;
        }
        aprove.verification.oldframework.Algebra.Polynomials.ConstraintType constantCt = ct;
        OrderPoly<MbyN> poly = atom.getLeftPoly();
        this.flatteningVisitorOuter.applyTo(poly);

        // there is no need to handle coefficients of variables x,y,.. if there
        // are none.
        if (uqVars.size() > 0) {
            Map<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> map =
                poly.getMonomials(this.pair);
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> entry
                    : map.entrySet()) {
                GMonomial<GPolyVar> monomial = entry.getKey();
                GPoly<MbyN, GPolyVar> coeffPoly = entry.getValue();
                for (GPolyVar var : uqVars) {
                    if (monomial.getExponents().containsKey(var)) {
                        this.flatteningVisitorInner.applyTo(coeffPoly);
                        Map<GMonomial<GPolyVar>, MbyN> coeffMap =
                            coeffPoly.getMonomials(this.ringC, this.monoid);
                        localConstraints =
                            this.getFormulaFactory().buildAnd(localConstraints,
                                this.createConstraint(coeffMap, coeffCt));
                    }
                }
            }
        }

        // handle the constant part
        GPoly<MbyN, GPolyVar> constant = poly.getConstantPart(this.pair);
        this.flatteningVisitorInner.applyTo(constant);
        Formula<Diophantine> constConstraint =
            this.createConstraint(constant.getMonomials(
                    this.ringC, this.monoid), constantCt);
        localConstraints = this.getFormulaFactory().buildAnd(
                localConstraints, constConstraint);
        this.buildAnd(this.getFormula(), localConstraints);
    }

    /**
     * Create constraints out of the given map and constraint type.
     * @param map Each monomial has a coefficient.
     * @param ct The constraint type.
     * @return The SimplePolyConstraint based on the OPC (provided by the map
     * and constraint type).
     */
    private Formula<Diophantine> createConstraint(
            final Map<GMonomial<GPolyVar>, MbyN> map, final ConstraintType ct) {
        // The map might describe a polynomial like
        // 2ab - ab + b >= 0 where a ranges over the default range and b
        // is a boolean variable.
        SimplePolynomial simplePoly;

        if (this.denominator != null) {
            BigInteger defaultRangeInt =
                this.defaultRange.getList().get(0).y.getNumerator();
            Map<GPolyVar, Boolean> boolMap =
                new LinkedHashMap<GPolyVar, Boolean>();
            Map<GMonomial<GPolyVar>, Integer> numVarsMap =
                new LinkedHashMap<GMonomial<GPolyVar>, Integer>();
            simplePoly = SimplePolynomial.ZERO;
            // encode m/n for a fixed value of n.

            // find the exponent for n in the common denominator
            // (a/n)^3 + b/n*c/n has a common denominator of n^3 (where 3 is the
            // maximal number of variables in the monomials).
            int exponent = -1;
            for (Map.Entry<GMonomial<GPolyVar>, MbyN> entry : map.entrySet()) {
                int numVars = 0;
                for (Map.Entry<GPolyVar, BigInteger> entry2
                        : entry.getKey().getExponents().entrySet()) {
                    GPolyVar var = entry2.getKey();
                    Boolean bool = boolMap.get(var);
                    if (bool == null) {
                        bool = false;
                        OPCRange<MbyN> range;
                        if (this.ranges != null) {
                            range = this.ranges.get(var);
                        } else {
                            range = this.defaultRange;
                        }
                        if (range != null) {
                            BigInteger rangeInt =
                                range.getList().get(0).y.getNumerator();
                            if (!rangeInt.equals(defaultRangeInt)) {
                                bool = true;
                                if (Globals.useAssertions) {
                                    assert (rangeInt.equals(BigInteger.ONE));
                                }
                            }
                        }
                        boolMap.put(var, bool);
                    }
                    if (!bool) {
                        numVars += entry2.getValue().intValue();
                    }
                }
                if (numVars > exponent) {
                    exponent = numVars;
                }
                numVarsMap.put(entry.getKey(), numVars);
            }
            for (Map.Entry<GMonomial<GPolyVar>, MbyN> entry : map.entrySet()) {
                Map<String, Integer> exponents =
                    new LinkedHashMap<String, Integer>();
                int numVars = numVarsMap.get(entry.getKey());
                SimplePolynomial mon =
                    SimplePolynomial.create(
                            entry.getValue().getNumerator().multiply(
                                    this.denominator.pow(exponent - numVars)));
                for (Map.Entry<GPolyVar, BigInteger> entry2
                        : entry.getKey().getExponents().entrySet()) {
                    exponents.put(this.getNum(entry2.getKey()).getName(),
                            entry2.getValue().intValue());
                }
                IndefinitePart indef = IndefinitePart.create(exponents);
                mon = mon.times(indef);
                simplePoly = simplePoly.plus(mon);
            }
        } else {
            // encode m/n for n ranging over several values.

            // replace variables a by n/m and find the common denominator
            Map<GPolyVar, BigInteger> cd =
                new LinkedHashMap<GPolyVar, BigInteger>();
            for (Map.Entry<GMonomial<GPolyVar>, MbyN> entry : map.entrySet()) {
                MbyN coeff = entry.getValue();
                GMonomial<GPolyVar> mon = entry.getKey();
                if (!coeff.equals(this.ringC.zero())) {
                    for (Map.Entry<GPolyVar, BigInteger> entry2
                            : mon.getExponents().entrySet()) {
                        GPolyVar var = entry2.getKey();
                        BigInteger exp = entry2.getValue();
                        GPolyVar denom = this.getDenom(var);
                        BigInteger cdExp = cd.get(denom);
                        if (cdExp == null || exp.compareTo(cdExp) > 0) {
                            cd.put(denom, exp);
                        }
                    }
                }
            }

            // multiply each monomial by the common denominator
            Map<IndefinitePart, BigInteger> newMap =
                new LinkedHashMap<IndefinitePart, BigInteger>(map.size());
            for (Map.Entry<GMonomial<GPolyVar>, MbyN> entry : map.entrySet()) {
                MbyN coeff = entry.getValue();
                GMonomial<GPolyVar> mon = entry.getKey();
                if (!coeff.equals(this.ringC.zero())) {
                    // make a copy of the common denominator. For cd = (x^2)y and a
                    // monomial (abcd)/(xy) the factor will later be factor = x
                    // (resulting in abcdx = abcd/xy * (x^2)y).
                    Map<String, Integer> factor =
                        new LinkedHashMap<String, Integer>(cd.size());
                    for (Map.Entry<GPolyVar, BigInteger> cdEntry
                            : cd.entrySet()) {
                        factor.put(
                                cdEntry.getKey().getName(),
                                cdEntry.getValue().intValue());
                    }

                    // the new monomial will be stored here
                    Map<String, Integer> newMon =
                        new LinkedHashMap<String, Integer>(
                                mon.getExponents().size());
                    for (Map.Entry<GPolyVar, BigInteger> entry2
                            : mon.getExponents().entrySet()) {
                        GPolyVar varMon = entry2.getKey();
                        BigInteger expMon = entry2.getValue();
                        GPolyVar numerator = this.getNum(varMon);
                        newMon.put(numerator.getName(), expMon.intValue());
                        GPolyVar denom = this.getDenom(varMon);
                        BigInteger expCD = cd.get(denom);
                        BigInteger diff = expCD.subtract(expMon);
                        if (diff.signum() > 0) {
                            // e.g. denom=x with cd=x^2, only x remains
                            factor.put(denom.getName(), diff.intValue());
                        } else {
                            // the current variable^exp completely cancels out
                            // the effect of the common denominator
                            factor.remove(denom.getName());
                        }
                    }
                    // now create the new monomial which is the coefficient
                    // times the numerators times the (just defined) "factor"
                    newMon.putAll(factor); // these variables are disjoint

                    IndefinitePart indefPart = IndefinitePart.create(newMon);
                    if (Globals.useAssertions) {
                        assert (coeff.getDenominator().equals(BigInteger.ONE));
                    }
                    newMap.put(indefPart, coeff.getNumerator());
                }
            }

            simplePoly = SimplePolynomial.create(newMap);
        }
        Diophantine dio = Diophantine.create(simplePoly, ct);
        return this.getFormulaFactory().buildTheoryAtom(dio);
    }

    /**
     * Create a fresh variable which will be used as the numerator for the
     * given variable.
     * @param varMon The variable of the OPC.
     * @return A fresh variable.
     */
    private GPolyVar getNum(final GPolyVar varMon) {
        GPolyVar result = this.numerators.get(varMon);
        if (result == null) {
            result = this.newVar();
            this.numerators.put(varMon, result);
            OPCRange<MbyN> range;
            if (this.ranges != null) {
                range = this.ranges.get(varMon);
            } else {
                range = this.defaultRange;
            }
            if (range == null) {
                range = this.defaultRange;
            }
            BigInteger numRange = range.getList().get(0).x.getNumerator();
            this.newRanges.put(result.getName(), numRange);
        }
        return result;
    }

    /**
     * Create a fresh variable which will be used as the denominator for the
     * given variable.
     * @param varMon The variable of the OPC.
     * @return A fresh variable.
     */
    private GPolyVar getDenom(final GPolyVar varMon) {
        GPolyVar result = this.denominators.get(varMon);
        if (result == null) {
            result = this.newVar();
            this.denominators.put(varMon, result);
            OPCRange<MbyN> range;
            if (this.ranges != null) {
                range = this.ranges.get(varMon);
            } else {
                range = this.defaultRange;
            }
            if (range == null) {
                range = this.defaultRange;
            }
            BigInteger denomRange = range.getList().get(0).y.getNumerator();
            this.newRanges.put(result.getName(), denomRange);
            // take care that the denominator is > 0!
            SimplePolynomial simplePoly =
                SimplePolynomial.create(result.getName());
            Diophantine dio = Diophantine.create(simplePoly, ConstraintType.GT);
            Formula<Diophantine> newFormula =
                this.getFormulaFactory().buildTheoryAtom(dio);
            this.buildAnd(this.getFormula(), newFormula);
        }
        return result;
    }

    /**
     * @return the ranges for the variables in the formula.
     */
    public Map<String, BigInteger> getRanges() {
        return this.newRanges;
    }

    /**
     * @return the numerators.
     */
    public Map<GPolyVar, GPolyVar> getNumerators() {
        if (Globals.useAssertions) {
            assert (this.numerators.keySet().equals(
                    this.denominators.keySet()) || this.denominator != null);
        }
        return this.numerators;
    }

    /**
     * @return the denominators.
     */
    public Map<GPolyVar, GPolyVar> getDenominators() {
        if (Globals.useAssertions) {
            assert (this.numerators.keySet().equals(
                    this.denominators.keySet()) || this.denominator != null);
        }
        return this.denominators;
    }
 }
