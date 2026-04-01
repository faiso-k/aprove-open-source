/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * An ExtractFormulaVisitor can be used to convert the given OrderPolyConstraint
 * to some propositional formula using Absolute Positiveness.
 * @author cotto
 */
public class RATExtractFormulaVisitor extends ConstraintVisitor.ConstraintVisitorSkeleton<PoT> {
    /**
     * This ring is used to operate on the coefficients.
     */
    private Ring<PoT> ringC;

    /**
     * This factory is used to generate propositional formula.
     */
    private FormulaFactory<None> factory =
        new FullSharingFlatteningFactory<None>();

    /**
     * Every new variable has a unique suffix defined by this number.
     */
    private int varCount;

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
     * The formula will be stored here.
     */
    private Formula<None> formula;

    /**
     * Remember a' = 2^k a. (a is mapped to a').
     */
    private Map<GPolyVar, GPolyVar> changed = new LinkedHashMap<GPolyVar, GPolyVar>();

    /**
     * The ranges for the variables in the original constraints.
     */
    private Map<GPolyVar, OPCRange<PoT>> ranges;

    /**
     * The ranges for the variables in the resulting simple poly constraints.
     */
    private Map<GPolyVar, OPCRange<PoT>> newRanges =
        new LinkedHashMap<GPolyVar, OPCRange<PoT>>();

    /**
     * The smallest exponent that may be chosen for the variables.
     */
    private int expMin;

    /**
     * The greatest exponent that may be chosen for the variables.
     */
    private int expMax;

    /**
     * This range will be used for variables a' that result from variables a
     * with the default range.
     */
    private final OPCRange<PoT> newDefaultRange;

    /**
     * This factory operates on circuits and provides new circuits for the
     * results of operations on these.
     */
    private ArithmeticCircuitFactory circuitFactory;

    /**
     * The binarizer can create new circuits for variables and constants.
     */
    private IndefiniteBinarizer<String> binarizer;

    /**
     * A variable converter that can store information about the connection
     * between OPC variables and propositional variables.
     */
    private VariableConverterPoT varConv;

    /**
     * Remember the connection between a and a'.
     */
    private Map<GPolyVar, Pair<GPolyVar, PoT>> transformed =
        new LinkedHashMap<GPolyVar, Pair<GPolyVar, PoT>>();

    /**
     * The default range as a OPCRange.
     */
    private OPCRange<PoT> defaultRange;

    /**
     * Remember what variables already were translated.
     */
    private Map<GPolyVar, Pair<PolyCircuit, PolyCircuit>> varCache =
        new LinkedHashMap<GPolyVar, Pair<PolyCircuit, PolyCircuit>>();

    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<PoT, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair;

    /**
     * Remember the quantifiers along the path to the atom.
     */
    private Stack<OPCQuantifier<PoT>> quantStack =
        new Stack<OPCQuantifier<PoT>>();

    /**
     * When negating a partial formula will be backed up here.
     */
    private Stack<Formula<None>> backup =
        new Stack<Formula<None>>();

    /**
     * Create a new ExtractFormulaVisitor.
     * @param ringCParam A ring over C (which is PoT here).
     * @param polyRingParam A ring over polynomials.
     * @param monoidParam A monoid over monomials over variables.
     * @param fvInner A flattening visitor for coefficient polynomials.
     * @param fvOuter A flattening visitor for order polynomials.
     * @param rangesParam The ranges for the variables.
     * @param min The smallest exponent that may be chosen for the variables.
     * @param max The greatest exponent that may be chosen for the variables.
     * @param varConvParam A variable converter that can store information about
     * the connection between OPC variables and propositional variables.
     */
    public RATExtractFormulaVisitor(final Ring<PoT> ringCParam,
            final Ring<GPoly<PoT, GPolyVar>> polyRingParam,
            final CMonoid<GMonomial<GPolyVar>> monoidParam,
            final FlatteningVisitor<PoT, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<PoT, GPolyVar>, GPolyVar> fvOuter,
            final Map<GPolyVar, OPCRange<PoT>> rangesParam,
            final int min,
            final int max,
            final VariableConverterPoT varConvParam) {
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
        this.formula = this.factory.buildConstant(true);
        this.binarizer = IndefiniteBinarizer.create(this.factory, null);
        this.circuitFactory = ArithmeticCircuitFactory.create(this.factory,
                new PoloSatConfigInfo());
        this.varConv = varConvParam;
        this.newDefaultRange = new OPCRange<PoT>(PoT.ONE, PoT.create(
                BigInteger.ONE, BigInteger.valueOf(max - min)));
        this.defaultRange = new OPCRange<PoT>(
                    PoT.create(BigInteger.ONE, BigInteger.valueOf(min)),
                    PoT.create(BigInteger.ONE, BigInteger.valueOf(max)));
    }

    /**
     * @return the collected formula.
     */
    public Formula<None> getFormula() {
        return this.formula;
    }

    /**
     * Start visiting the given constraint and clean up afterwards.
     * @param constraint The constraint that should be visited.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<PoT> applyToWithCleanup(final OrderPolyConstraint<PoT> constraint) {
        final OrderPolyConstraint<PoT> result = this.applyTo(constraint);
        this.circuitFactory = null;
        this.binarizer = null;
        this.factory = null;
        return result;
    }

    /**
     * @return the map giving information about the connection between a and a'.
     */
    public Map<GPolyVar, Pair<GPolyVar, PoT>> getTransformed() {
        return this.transformed;
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
        for (OPCQuantifier<PoT> elem : this.quantStack) {
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

        List<Formula<None>> subFormulae = new ArrayList<Formula<None>>();

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
                        Formula<None> newFormula =
                            this.createFormula(coeffMap, coeffCt);
                        subFormulae.add(newFormula);
                    }
                }
            }
        }

        // handle the constant part
        GPoly<PoT, GPolyVar> constant = poly.getConstantPart(this.pair);
        this.flatteningVisitorInner.applyTo(constant);
        Formula<None> constantFormula =
            this.createFormula(constant.getMonomials(
                    this.ringC, this.monoid), constantCt);
        subFormulae.add(constantFormula);
        subFormulae.add(this.formula);
        this.formula = this.factory.buildAnd(subFormulae);
        return atom;
    }

    /**
     * Create a formula out of the given map and constraint type.
     * @param map Each monomial has a coefficient.
     * @param ct The constraint type.
     * @return A Formula which represents the original OPC (given by the map
     * and constraint type).
     */
    private Formula<None> createFormula(
            final Map<GMonomial<GPolyVar>, PoT> map, final ConstraintType ct) {
        // The map might describe a polynomial like
        // 2ab - ab + b >= 0 where a ranges over the default range and b
        // is a boolean variable.

        // 1) replace all variables that have a non-integer value in the range
        // by a new variable.

        Map<GMonomial<GPolyVar>, PoT> newMap = this.transformVariables(map);

        // 2) convert the (new) constraints as described in the research notes
        return this.convertPolyConstraint(newMap, ct);
    }

    /**
     * Create a formula for the given constraint. Basically convert "p1 = p2"
     * and/or "p1 > p2" and take care to get representations for p1 and p2
     * first.
     * @param map The map defining the polynomial of the constraint.
     * @param ct The type of the constraint.
     * @return The formula for this constraint.
     */
    private Formula<None> convertPolyConstraint(
            final Map<GMonomial<GPolyVar>, PoT> map, final ConstraintType ct) {
        // the encoding only works on polynomial constraints without negative
        // coefficients, so move these over to the right side
        Map<GMonomial<GPolyVar>, PoT> left =
            new LinkedHashMap<GMonomial<GPolyVar>, PoT>();
        Map<GMonomial<GPolyVar>, PoT> right =
            new LinkedHashMap<GMonomial<GPolyVar>, PoT>();
        CoeffOrder<PoT> order = new PoTOrder();
        for (Map.Entry<GMonomial<GPolyVar>, PoT> entry : map.entrySet()) {
            PoT coeff = entry.getValue();
            int signum = order.signum(coeff);
            if (Globals.useAssertions) {
                assert (signum != 0 || entry.getKey().equals(
                        this.monoid.neutral()));
            }
            if (order.signum(coeff) < 0) {
                PoT invCoeff = this.ringC.getInverse(coeff);
                right.put(entry.getKey(), invCoeff);
            } else if (signum > 0) {
                // drop the constant part "+0"
                left.put(entry.getKey(), entry.getValue());
            }
        }
        Pair<PolyCircuit, PolyCircuit> leftEncoding = this.encodePoly(left);
        Pair<PolyCircuit, PolyCircuit> rightEncoding = this.encodePoly(right);
        Formula<None> encoding;
        List<Formula<None>> alternatives = new ArrayList<Formula<None>>();
        alternatives.addAll(this.encodeEQGTGE(leftEncoding, rightEncoding, ct));
        encoding = this.factory.buildOr(alternatives);
        return encoding;
    }

    /**
     * @param leftEncoding The encoding of the left side of the comparison.
     * @param rightEncoding The encoding of the right side of the comparison.
     * @param ct The constraint giving information if l=r, l>r or l>=r is
     * needed.
     * @return Formulae for l > r and/or l = r.
     */
    private Collection<Formula<None>> encodeEQGTGE(
            final Pair<PolyCircuit, PolyCircuit> leftEncoding,
            final Pair<PolyCircuit, PolyCircuit> rightEncoding,
            final ConstraintType ct) {
        PolyCircuit v1 = leftEncoding.x;
        PolyCircuit e1 = leftEncoding.y;
        PolyCircuit v2 = rightEncoding.x;
        PolyCircuit e2 = rightEncoding.y;
        PolyCircuit s1 = this.encodeShift(v1, e1);
        PolyCircuit s2 = this.encodeShift(v2, e2);
        Collection<Formula<None>> result = new LinkedHashSet<Formula<None>>(1);
        if (ct.equals(ConstraintType.EQ) || ct.equals(ConstraintType.GE)) {
            Formula<None> eq = this.circuitFactory.buildEQCircuit(
                        s1.getFormulae(), s2.getFormulae());
            result.add(eq);
        }
        if (ct.equals(ConstraintType.GE) || ct.equals(ConstraintType.GT)) {
            Formula<None> gt = this.circuitFactory.buildGTCircuit(
                    s1.getFormulae(), s2.getFormulae());
            result.add(gt);
        }
        return result;
    }

    /**
     * Encode the polynomial, which is a sum of products, according to the
     * research notes. This involves finding the representation of all factors
     * and addends first.
     * @param poly The polynomial.
     * @return The representation as a tuple of two formulae.
     */
    private Pair<PolyCircuit, PolyCircuit> encodePoly(
            final Map<GMonomial<GPolyVar>, PoT> poly) {
        if (poly.size() == 0) {
            return this.encodeConstant(BigInteger.ZERO);
        }
        Pair<PolyCircuit, PolyCircuit> addendOne = null;
        Pair<PolyCircuit, PolyCircuit> addendTwo = null;
        for (Map.Entry<GMonomial<GPolyVar>, PoT> entry : poly.entrySet()) {
            addendTwo = addendOne;
            if (!entry.getKey().equals(this.monoid.neutral())) {
                Pair<PolyCircuit, PolyCircuit> factorOne =
                    this.encodeMonomial(entry.getKey());
                Pair<PolyCircuit, PolyCircuit> factorTwo =
                    this.encodeCoeff(entry.getValue());
                addendOne = this.encodeOuterProduct(factorOne, factorTwo);
            } else {
                addendOne = this.encodeCoeff(entry.getValue());
            }
            if (addendTwo != null) {
                addendOne = this.encodeOuterSum(addendOne, addendTwo);
            }
        }
        return addendOne;
    }

    /**
     * @return the circuits for the constant of the type PoT.
     * @param value The constant value.
     */
    private Pair<PolyCircuit, PolyCircuit> encodeCoeff(final PoT value) {
        return new Pair<PolyCircuit, PolyCircuit>(
                this.binarizer.toCircuit(value.getPair().x),
                this.binarizer.toCircuit(value.getPair().y));
    }

    /**
     * Encode the monomial, so create circuits for each variable regarding the
     * respective power and build the product of these.
     * @param monomial The monomial.
     * @return A pair of circuits defining the monomial.
     */
    private Pair<PolyCircuit, PolyCircuit> encodeMonomial(
            final GMonomial<GPolyVar> monomial) {
        if (Globals.useAssertions) {
            assert (monomial.getExponents().size() > 0);
        }
        Pair<PolyCircuit, PolyCircuit> result = null;
        boolean first = true;
        for (Map.Entry<GPolyVar, BigInteger> entry
                : monomial.getExponents().entrySet()) {
            BigInteger exp = entry.getValue();
            GPolyVar var = entry.getKey();
            if (Globals.useAssertions) {
                assert (exp.signum() > 0);
            }
            Pair<PolyCircuit, PolyCircuit> circuitPair = this.encodeVariable(var);
            if (exp.compareTo(BigInteger.ONE) > 0) {
                circuitPair = this.encodePower(circuitPair, exp);
            }
            if (first) {
                first = false;
                result = circuitPair;
            } else {
                result = this.encodeOuterProduct(result, circuitPair);
            }
        }
        return result;
    }

    /**
     * @param base The base.
     * @param exponent The exponent.
     * @return the circuits for base^exponent.
     */
    private Pair<PolyCircuit, PolyCircuit> encodePower(
            final Pair<PolyCircuit, PolyCircuit> base,
            final BigInteger exponent) {
        if (Globals.useAssertions) {
            assert (exponent.compareTo(BigInteger.ONE) > 0);
        }
        BigInteger two = BigInteger.valueOf(2);
        Pair<PolyCircuit, PolyCircuit> result = this.encodeConstant(BigInteger.ONE);
        Pair<PolyCircuit, PolyCircuit> tmp = base;
        BigInteger exp = exponent;
        while (exp.signum() > 0) {
            if (exp.mod(two).equals(BigInteger.ONE)) {
                result = this.encodeOuterProduct(result, tmp);
            }
            exp = exp.divide(two);
            if (exp.signum() > 0) {
                tmp = this.encodeOuterProduct(tmp, tmp);
            } else {
                break;
                // somewhat ugly, but slightly more efficient
                // (saves the last check of the loop cond.)
            }
        }
        return result;
    }

    /**
     * Create the circuits defining the given constant.
     * @param m The constant.
     * @return a circuit for m = i*2^j (i odd).
     */
    private Pair<PolyCircuit, PolyCircuit> encodeConstant(final BigInteger m) {
        if (Globals.useAssertions) {
            assert (m.signum() >= 0);
        }
        if (m.signum() == 0) {
            PolyCircuit zero = this.binarizer.toCircuit(m);
            return new Pair<PolyCircuit, PolyCircuit>(zero, zero);
        } else {
            // m = i*2^j
            int lowBit = m.getLowestSetBit();
            BigInteger j = BigInteger.valueOf(lowBit);
            BigInteger i = m.shiftRight(lowBit);
            return new Pair<PolyCircuit, PolyCircuit>(
                    this.binarizer.toCircuit(i), this.binarizer.toCircuit(j));
        }
    }

    /**
     * Build a tuple of circuits that represent the variable of type 2^k.
     * @param var The variable to be represented.
     * @return A tuple of two circuits.
     */
    private Pair<PolyCircuit, PolyCircuit> encodeVariable(final GPolyVar var) {
        Pair<PolyCircuit, PolyCircuit> result = this.varCache.get(var);
        if (result != null) {
            return result;
        }
        // var is a variable of type 2^k
        TRSVariable coeffVar = this.createVariable();
        PolyCircuit coeff =
            this.binarizer.bin(coeffVar.getName(), BigInteger.ONE);
        TRSVariable expVar = this.createVariable();
        // max is the maximum allowed exponent for the variable
        if (Globals.useAssertions) {
            // the range for the variable must be 0 or 2^0 .. 2^k for some
            // non-negative k
            BigInteger minExp =
                this.newRanges.get(var).getList().get(0).x.getPair().y;
            assert (minExp.equals(BigInteger.ZERO));
        }
        BigInteger max = this.newRanges.get(var).getList().get(0).y.getPair().y;
        PolyCircuit exp;
        if (max.signum() > 0) {
            // if max is not (2^k - 1) for some k side constraints have to be
            // added.
            // Example: exp = a*2^0 + b*2^1 with max=2 may produce exp=3 with
            // a=b=1, this has to be disallowed.
            exp = this.binarizer.bin(expVar.getName(), max);
            List<Formula<None>> formulae =
                new ArrayList<Formula<None>>(
                        this.excludeUpperValues(max, exp.getFormulae()));
            formulae.add(this.formula);
            this.formula = this.factory.buildAnd(formulae);
        } else {
            // var ranges over 0 and 2^0
            exp = this.binarizer.toCircuit(BigInteger.ZERO);
        }
        Pair<PolyCircuit, PolyCircuit> circuitPair =
            new Pair<PolyCircuit, PolyCircuit>(coeff, exp);
        // give the variable converter information how the variable is encoded.
        this.varConv.put(var, circuitPair);
        this.varCache.put(var, circuitPair);
        return circuitPair;
    }

    /**
     * Helper method for allowing arbitrary natural ranges for
     * Diophantine variables, not only 2^k - 1. Generates clauses
     * that prohibit values greater than range.
     *
     * @param range maximum value allowed for the variable defined by formulae,
     * may be at most 2^formulae.size() - 1.
     * @param formulae tuple of formulae that is supposed to represent some
     * Diophantine variable.
     * @return conjuncts for enforcing that I(vars) <= range for
     * any model I of the circuit in construction.
     */
    private List<Formula<None>> excludeUpperValues(
            final BigInteger range,
            final List<Formula<None>> formulae) {
        int bits = formulae.size();
        if (Globals.useAssertions) {
            assert (bits >= range.bitLength());
        }

        BigInteger two = BigInteger.valueOf(2);
        BigInteger max = two.pow(bits).subtract(BigInteger.ONE);

        if (range.equals(max)) {
            return Collections.<Formula<None>>emptyList();
        }

        List<Formula<None>> notVars = new ArrayList<Formula<None>>(bits);
        for (int i = 0; i < formulae.size(); ++i) {
            notVars.add(this.factory.buildNot(formulae.get(i)));
        }

        List<Formula<None>> result =
            new ArrayList<Formula<None>>(max.subtract(range).intValue());
        for (BigInteger i = range.add(BigInteger.ONE);
            i.compareTo(max) <= 0; i = i.add(BigInteger.ONE)) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(bits);
            for (int j = 0; j < bits; ++j) {
                if (i.testBit(j)) {
                    disjuncts.add(notVars.get(j));
                } else {
                    disjuncts.add(formulae.get(j));
                }
            }
            result.add(this.factory.buildOr(disjuncts));
        }
        return result;
    }

    /**
     * Encode the product of two atomic expressions.
     * @param factorOne The first factor.
     * @param factorTwo The second factor.
     * @return The product as a tuple of two formulae.
     */
    private Pair<PolyCircuit, PolyCircuit> encodeOuterProduct(
            final Pair<PolyCircuit, PolyCircuit> factorOne,
            final Pair<PolyCircuit, PolyCircuit> factorTwo) {
        PolyCircuit v1 = factorOne.x;
        PolyCircuit e1 = factorOne.y;
        PolyCircuit v2 = factorTwo.x;
        PolyCircuit e2 = factorTwo.y;
        PolyCircuit v = this.circuitFactory.buildTimesCircuit(v1, v2);
        PolyCircuit e = this.circuitFactory.buildPlusCircuit(e1, e2);
        return new Pair<PolyCircuit, PolyCircuit>(v, e);
    }

    /**
     * Encode the sum product of two atomic expressions.
     * @param addendOne The first addend.
     * @param addendTwo The second addend.
     * @return The sum as a tuple of two formulae.
     */
    private Pair<PolyCircuit, PolyCircuit> encodeOuterSum(
            final Pair<PolyCircuit, PolyCircuit> addendOne,
            final Pair<PolyCircuit, PolyCircuit> addendTwo) {
        PolyCircuit v1 = addendOne.x;
        PolyCircuit e1 = addendOne.y;
        PolyCircuit v2 = addendTwo.x;
        PolyCircuit e2 = addendTwo.y;

        // e2 - e1
        Pair<PolyCircuit, Formula<None>> minusOne =
            this.encodeMinus(e2, e1);

        // The maximum value of the minusOne circuit is very pessimistic.
        // Because we know that we do not calculate a-b for b>a we may use
        // wrong values for the case a-b with b>a.
        // Because (e2 - e1) ranges from e2 to 0 and we do not know a _minimum_
        // value of e1, the maximum value of the term is e2.
        BigInteger newMax = e2.getMax();
        minusOne.x = new PolyCircuit(minusOne.x.getFormulae(), newMax);

        // v2 << (e2 - e1)
        PolyCircuit shiftOne = this.encodeShift(v2, minusOne.x);

        // v1 + (v2 << (e2 - e1))
        PolyCircuit resultOne =
            this.circuitFactory.buildPlusCircuit(v1, shiftOne);

        // neg(e2 - e1)
        PolyCircuit minusTwo = this.negate(minusOne.x);

        // 1
        PolyCircuit one = this.binarizer.toCircuit(BigInteger.ONE);

        // neg(e2 - e1) + 1
        minusTwo = this.circuitFactory.buildPlusCircuit(minusTwo, one);

        // here, too, the maximum value is very pessimistic for the relevant
        // case e1 >= e2.
        newMax = e1.getMax();
        minusTwo = new PolyCircuit(minusTwo.getFormulae(), newMax);


        // v1 << (neg(e2 - e1) + 1)
        PolyCircuit shiftTwo = this.encodeShift(v1, minusTwo);

        // (v1 << ((e2 - e1) + 1)) + v2
        PolyCircuit resultTwo =
            this.circuitFactory.buildPlusCircuit(shiftTwo, v2);

        List<Formula<None>> formulaeOne = resultOne.getFormulae();
        List<Formula<None>> formulaeTwo = resultTwo.getFormulae();
        int sizeOne = formulaeOne.size();
        int sizeTwo = formulaeTwo.size();
        int length = Math.max(sizeOne, sizeTwo);
        Formula<None> zero = this.factory.buildConstant(false);
        List<Formula<None>> newFormulaeOne =
            this.pad(formulaeOne, length, zero);
        List<Formula<None>> newFormulaeTwo =
            this.pad(formulaeTwo, length, zero);
        List<Formula<None>> result = new ArrayList<Formula<None>>(length);

        Formula<None> comparison = minusOne.y;
        BigInteger maxValue = resultOne.getMax().max(resultTwo.getMax());

        for (int i = 0; i < length; i++) {
            Formula<None> f1 = newFormulaeOne.get(i);
            Formula<None> f2 = newFormulaeTwo.get(i);
            result.add(this.factory.buildIte(comparison, f1, f2));
        }
        PolyCircuit v = new PolyCircuit(result, maxValue);

        formulaeOne = e1.getFormulae();
        formulaeTwo = e2.getFormulae();
        sizeOne = formulaeOne.size();
        sizeTwo = formulaeTwo.size();
        length = Math.max(sizeOne, sizeTwo);
        newFormulaeOne = this.pad(formulaeOne, length, zero);
        newFormulaeTwo = this.pad(formulaeTwo, length, zero);
        result = new ArrayList<Formula<None>>(length);

        for (int i = 0; i < length; i++) {
            Formula<None> f1 = newFormulaeOne.get(i);
            Formula<None> f2 = newFormulaeTwo.get(i);
            result.add(this.factory.buildIte(comparison, f1, f2));
        }
        maxValue = e1.getMax().max(e2.getMax());
        PolyCircuit e = new PolyCircuit(result, maxValue);
        return new Pair<PolyCircuit, PolyCircuit>(v, e);
    }

    /**
     * @return a formula list of length "length" based on the list "target"
     * where elements "pad" are padded to the end of the list (most significant
     * bits).
     * @param target The formula list to pad.
     * @param length The length to pad to.
     * @param pad The element to pad with.
     */
    private List<Formula<None>> pad(
            final List<Formula<None>> target,
            final int length,
            final Formula<None> pad) {
        int size = target.size();
        if (Globals.useAssertions) {
            assert (size <= length);
        }
        if (length == size) {
            return target;
        }
        List<Formula<None>> result = new ArrayList<Formula<None>>(target);
        for (int i = size; i < length; i++) {
            result.add(pad);
        }
        return result;
    }

    /**
     * Negate every bit of the given circuit.
     * @param target The target to negate.
     * @return A polycircuit with all bits negated.
     */
    private PolyCircuit negate(final PolyCircuit target) {
        return this.negate(target, target.getFormulae().size());
    }

    /**
     * Negate every bit of the given circuit. Pad with ONEs to the left.
     * @param target The target to negate.
     * @param size The minimal size of the resulting formula list.
     * @return A polycircuit with all bits negated.
     */
    private PolyCircuit negate(final PolyCircuit target, final int size) {
        List<Formula<None>> formulae = target.getFormulae();
        int formulaeLength = formulae.size();
        int length = Math.max(formulaeLength, size);
        List<Formula<None>> result = new ArrayList<Formula<None>>(length);
        for (Formula<None> subFormula : formulae) {
            result.add(this.factory.buildNot(subFormula));
        }
        // pad with 1s
        Formula<None> one = this.factory.buildConstant(true);
        for (int i = formulae.size(); i < length; i++) {
            result.add(one);
        }
        // the greatest possible value is defined by the number of bits.
        BigInteger two = BigInteger.valueOf(2);
        BigInteger max = two.pow(formulae.size()).subtract(BigInteger.ONE);
        return new PolyCircuit(result, max);
    }

    /**
     * Encode q - r using addition (q + neg(r) + 1 without the new carry bit).
     * The result is only correct for q >= r (take care of the maximum value for
     * the returned circuit, which is also correct (but quite high) for q < r!).
     * @param q The minuend.
     * @param r The subtrahend.
     * @return The difference q - r in the first component and the last carry
     * bit as the second component.
     */
    private Pair<PolyCircuit, Formula<None>> encodeMinus(
            final PolyCircuit q,
            final PolyCircuit r) {
        int size = Math.max(q.getFormulae().size(), r.getFormulae().size());

        Formula<None> zero = this.factory.buildConstant(false);

        // negate r, pad with 1s to the left
        // 010 - 10 will get 010 + 101 (not 010 + 001)
        PolyCircuit rNeg = this.negate(r, size);
        List<Formula<None>> rnF = rNeg.getFormulae();
        List<Formula<None>> rF = this.pad(r.getFormulae(), size, zero);
        List<Formula<None>> qF = this.pad(q.getFormulae(), size, zero);
        List<Formula<None>> result = new ArrayList<Formula<None>>(size);
        if (Globals.useAssertions) {
            assert (size > 0);
        }
        // build the first two elements manually
        // q0 xor r0
        result.add(this.factory.buildXor(qF.get(0), rF.get(0)));

        //q0 v -r0
        Formula<None> lastCarry = this.factory.buildOr(qF.get(0), rnF.get(0));
        for (int i = 1; i < size; i++) {
            final int three = 3; // code style is annoying from time to time
            List<Formula<None>> list = new ArrayList<Formula<None>>(three);
            list.add(lastCarry);
            list.add(qF.get(i));
            list.add(rnF.get(i));
            result.add(this.factory.buildXor(list));
            lastCarry =
                this.circuitFactory.build2or3Circuit(
                        qF.get(i), rnF.get(i), lastCarry);
        }
        // the maximum value is not q.getMax(), because with q<r things get wild
        PolyCircuit diff =
            new PolyCircuit(result, AProVEMath.power(2, size) - 1);
        return new Pair<PolyCircuit, Formula<None>>(diff, lastCarry);
    }

    /**
     * Create a circuit that represents the result of q shifted by r.
     * @param q The first circuit.
     * @param r The second circuit.
     * @return A circuit for q << r.
     */
    private PolyCircuit encodeShift(final PolyCircuit q, final PolyCircuit r) {
        // build 2^r q
        PolyCircuit result = this.circuitFactory.buildPowerOfTwo(r);
        result = this.circuitFactory.buildTimesCircuit(result, q);
        return result;
    }

    /**
     * @return A new variable used for side conjuncts.
     */
    private TRSVariable createVariable() {
        this.varCount++;
        String name = "sideVariable_" + this.varCount;
        return TRSTerm.createVariable(name);
    }

    /**
     * Transform the monomials so that every variable ranges only over natural
     * numbers. Pay attention to correction factors (when some changed variable
     * does not occur in a monomial).
     * @param map The map containing the monomials.
     * @return The new monomial and information about the changed variables.
     */
    private Map<GMonomial<GPolyVar>, PoT> transformVariables(
            final Map<GMonomial<GPolyVar>, PoT> map) {
        Map<GMonomial<GPolyVar>, PoT> newMap =
            new LinkedHashMap<GMonomial<GPolyVar>, PoT>(map.size());
        // remember what variables were replaced in this polynomial in order to
        // calculate the correction later
        Map<GPolyVar, BigInteger> localChanges =
            new LinkedHashMap<GPolyVar, BigInteger>();
        // take a look at every monomial
        for (Map.Entry<GMonomial<GPolyVar>, PoT> entry : map.entrySet()) {
            // as the variables may be changed, construct a new map for this
            // monomial
            Map<GPolyVar, BigInteger> newMonomial =
                new LinkedHashMap<GPolyVar, BigInteger>();

            // take a look at every variable in the monomial
            for (Map.Entry<GPolyVar, BigInteger> innerEntry
                    : entry.getKey().getExponents().entrySet()) {
                GPolyVar var = innerEntry.getKey();
                // did we already transform this variable?
                GPolyVar newVar = this.changed.get(var);
                if (newVar == null) {
                    // no, so do it now
                    newVar = this.transformSingleVariable(var);
                }
                if (!var.equals(newVar)) {
                    BigInteger oldExp = localChanges.get(newVar);
                    if (oldExp == null) {
                        localChanges.put(newVar, innerEntry.getValue());
                    }
                }
                // newVar now is a variable that ranges over natural numbers,
                // this may be identical to var!

                BigInteger exponent = innerEntry.getValue();
                // perhaps the variable was already replaced before, but not as
                // often as the current exponent demands?
                BigInteger oldExp = localChanges.get(newVar);
                if (oldExp != null && exponent.compareTo(oldExp) > 0) {
                    localChanges.put(newVar, exponent);
                }

                // change the monomial accordingly
                if (newVar != null) {
                    // the variable has been transformed
                    newMonomial.put(newVar, exponent);
                } else {
                    newMonomial.put(var, exponent);
                }
            }
            PoT coeff = entry.getValue();
            newMap.put(new GMonomial<GPolyVar>(newMonomial), coeff);
        }

        // All variables have been handled and now newMonomial is complete
        // apart from the coefficient. If some variable that was changed
        // before did not occur in a monomial the corresponding coefficient has
        // to be adapted.
        PoT minimalCorrection = null;
        CoeffOrder<PoT> order = new PoTOrder();
        for (Map.Entry<GMonomial<GPolyVar>, PoT> entry : newMap.entrySet()) {
            PoT coeff = entry.getValue();
            if (!coeff.equals(this.ringC.zero())) {
                // there is no need to multiply something to 0.
                GMonomial<GPolyVar> mon = entry.getKey();
                // collect the (new) variables that do _not_ occur in the
                // current monomial
                Map<GPolyVar, BigInteger> notIncluded =
                    new LinkedHashMap<GPolyVar, BigInteger>(localChanges);
                for (Map.Entry<GPolyVar, BigInteger> innerEntry
                        : mon.getExponents().entrySet()) {
                    GPolyVar var = innerEntry.getKey();
                    BigInteger exp = innerEntry.getValue();
                    BigInteger newExp = notIncluded.get(var);
                    if (newExp != null) {
                        newExp = newExp.subtract(exp);
                    } else {
                        newExp = BigInteger.ZERO;
                    }
                    if (newExp.signum() == 0) {
                        notIncluded.remove(var);
                    } else {
                        notIncluded.put(var, newExp);
                    }
                }
                PoT localCorrection = PoT.ONE;
                for (Map.Entry<GPolyVar, BigInteger> innerEntry
                        : notIncluded.entrySet()) {
                    // The old variable a allows the value 1/2^k for some k>0,
                    // so correct the new monomial (where this variable a does
                    // not occur) by 2^k (where 1/2^k is the lower end of the
                    // range).
                    GPolyVar var = innerEntry.getKey();
                    BigInteger exp = innerEntry.getValue();
                    OPCRange<PoT> range = this.ranges.get(var);
                    PoT correction;
                    if (range != null) {
                        correction = range.getList().get(0).x;
                    } else {
                        correction = PoT.create(BigInteger.ONE, BigInteger
                                .valueOf(-this.expMin));
                    }
                    PoT orig = correction;
                    for (BigInteger i = BigInteger.ONE; i.compareTo(exp) < 0;
                            i = i.add(BigInteger.ONE)) {
                        correction = this.ringC.times(correction, orig);
                    }
                    coeff = this.ringC.times(coeff, correction);
                    localCorrection =
                        this.ringC.times(localCorrection, correction);
                }
                if (minimalCorrection == null) {
                    minimalCorrection = localCorrection;
                } else if (order.signum(this.ringC.minus(
                        minimalCorrection, localCorrection)) > 0) {
                    minimalCorrection = localCorrection;
                }
                if (!coeff.equals(entry.getValue())) {
                    newMap.put(entry.getKey(), coeff);
                }
            }
        }
        if (minimalCorrection != null && !minimalCorrection.equals(PoT.ONE)) {
            PoT negated = PoT.create(minimalCorrection.getPair().x,
                    minimalCorrection.getPair().y.negate());
            for (Map.Entry<GMonomial<GPolyVar>, PoT> e : newMap.entrySet()) {
                newMap.put(e.getKey(), this.ringC.times(e.getValue(), negated));
            }
        }
        return newMap;
    }

    /**
     * Investigate the given variable and create a new variable which only
     * ranges over natural numbers if necessary.
     * @param var The variable that may range over non-natural numbers.
     * @return A variable that only ranges over natural numbers.
     */
    private GPolyVar transformSingleVariable(final GPolyVar var) {
        GPolyVar newVar = var;
        int min;
        int max;
        OPCRange<PoT> range = this.ranges.get(var);
        OPCRange<PoT> newRange;
        // shift 1/4..8 (min -2, max 3) to 1..32 (min 0, max 5)
        if (range != null) {
            min = range.getList().get(0).x.getPair().y.intValue();
            max = range.getList().get(0).y.getPair().y.intValue();
            BigInteger newExp = BigInteger.valueOf(max - min);
            newRange = new OPCRange<PoT>(PoT.ONE, // 1*2^0
                    PoT.create(BigInteger.ONE, // 1*2^(max-min)
                            newExp));
        } else {
            min = this.expMin;
            max = this.expMax;
            newRange = this.newDefaultRange;
        }
        if (min < 0) {
            // the variable a ranges over some non-natural number,
            // so create 2^min a' = a.
            newVar = this.createPrimedVar(var);
            this.changed.put(var, newVar);
            // a = a' * correction = a' * 2^min = a' * 1/(2^abs(min))
            PoT correction =
                PoT.create(BigInteger.ONE, BigInteger.valueOf(min));
            Pair<GPolyVar, PoT> transPair =
                new Pair<GPolyVar, PoT>(var, correction);
            this.transformed.put(newVar, transPair);
            this.newRanges.put(newVar, newRange);
        } else if (range != null) {
            // nothing to change, just move the range over to the
            // new map
            this.newRanges.put(var, range);
            Pair<GPolyVar, PoT> transPair =
                new Pair<GPolyVar, PoT>(var, PoT.ONE);
            this.transformed.put(var, transPair);
        } else {
            // the default range is used, so mention it explicitely.
            this.newRanges.put(var, this.defaultRange);
            Pair<GPolyVar, PoT> transPair =
                new Pair<GPolyVar, PoT>(var, PoT.ONE);
            this.transformed.put(var, transPair);
        }
        return newVar;
    }

    /**
     * @param var The old variable (a).
     * @return The new variable (a').
     */
    private GPolyVar createPrimedVar(final GPolyVar var) {
        String name = var.getName();
        this.varCount++;
        String newName = name + "_" + this.varCount;
        return GAtomicVar.createVariable(newName);
    }

    /**
     * Negate the result which is stored in this.formula. The original formula
     * is stored in this.backup.
     * @param not The not node.
     * @param newConstraint the new subconstraint.
     * @return not itself.
     */
    @Override
    public OrderPolyConstraint<PoT> caseNot(
            final OPCNot<PoT> not,
            final OrderPolyConstraint<PoT> newConstraint) {
        if (Globals.useAssertions) {
            assert (not.getSub().equals(newConstraint));
        }
        if (this.backup != null) {
            // negate the formula for this and node
            // (the previous formula is only stored in backup!).
            this.formula = this.factory.buildNot(this.formula);
            // re-apply the backup
            this.formula =
                this.factory.buildAnd(this.backup.pop(), this.formula);
        }
        return not;
    }

    /**
     * A not node is being visited.
     * @param not The not node.
     */
    @Override
    public void fcaseNot(final OPCNot<PoT> not) {
        if (Globals.useAssertions) {
            assert (not.getSub() instanceof OPCAnd
                    || not.getSub() instanceof OPCAtom)
            : "NOT may only be used in front of AND or an Atom";
        }
        // the to-be-constructed formula for the nodes behind this and node
        // must be negated. To do that first backup the current formula,
        // collect the formula for the subnodes and negate that when
        // construction is finished. After that restore the old formula
        // from the backup. See caseAnd().
        this.backup.push(this.formula);
        this.formula = this.factory.buildConstant(true);
    }

    /**
     * An existential quantifier is visited.
     * As only one existential quantifier is allowed and it must be at the root
     * of the formula, this will be checked.
     * @param quant The quantifier node.
     */
    @Override
    public void fcaseQuantifierE(final OPCQuantifierE<PoT> quant) {
        if (Globals.useAssertions) {
            assert (this.quantStack.empty())
            : "A existential quantifier may only appear at the formula's root!";
        }
        this.quantStack.push(quant);
    }

    /**
     * Remove the quantifier from the stack representing the path, as the
     * path starting with this quantifier is already handled now.
     * @param quant The quant node.
     * @param newConstraint the new and old sub constraint.
     * @return quant itself.
     */
    @Override
    public OPCQuantifierE<PoT> caseQuantifierE(
            final OPCQuantifierE<PoT> quant,
            final OrderPolyConstraint<PoT> newConstraint) {
        OPCQuantifier<PoT> pop = this.quantStack.pop();
        if (Globals.useAssertions) {
            assert (quant.equals(pop));
            if (!quant.getInnerConstraint().equals(newConstraint)) {
                if (Globals.DEBUG_COTTO) {
                    System.out.println("doof.");
                }
            }
            assert (quant.getInnerConstraint().equals(newConstraint));
        }
        return quant;
    }

    /**
     * An or node is visited, not supported.
     * @param or The or node.
     */
    @Override
    public void fcaseOr(final OPCOr<PoT> or) {
        if (Globals.useAssertions) {
            assert (false) : "Not supported.";
        }
    }

    /**
     * A universal quantifier is visited. This visitor only allows these
     * quantifiers directly in front of a atom node.
     * @param quant The quantifier node.
     */
    @Override
    public void fcaseQuantifierA(final OPCQuantifierA<PoT> quant) {
        OrderPolyConstraint<PoT> inner = quant.getInnerConstraint();
        if (Globals.useAssertions) {
            assert (inner instanceof OPCAtom)
            : "A universal quantifier may only be placed in front of an atom!";
            Set<GPolyVar> vars = new LinkedHashSet<GPolyVar>();
            for (OPCQuantifier<PoT> elem : this.quantStack) {
                vars.addAll(elem.getQuantifiedVariables());
            }
            assert (!vars.removeAll(quant.getQuantifiedVariables()))
            : "The quantified variables must be disjoint in every subformula";
        }
        this.quantStack.push(quant);
    }

    /**
     * Remove the quantifier from the stack representing the path, as the
     * path starting with this quantifier is already handled now.
     * @param quant The quant node.
     * @param newConstraint The new and old sub constraint.
     * @return quant itself.
     */
    @Override
    public OrderPolyConstraint<PoT> caseQuantifierA(
            final OPCQuantifierA<PoT> quant,
            final OrderPolyConstraint<PoT> newConstraint) {
        OPCQuantifier<PoT> pop = this.quantStack.pop();
        if (Globals.useAssertions) {
            assert (quant.getInnerConstraint().equals(newConstraint));
            assert (quant.equals(pop));
        }
        return quant;
    }
}
