package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.Atom.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represents a polynomial constraint.
 * @author Matthias Hoelzel
 */
public class PolynomialConstraint {
    /**
     * Enumeration of constraint types.
     */
    public enum PolynomialConstraintType {
        /**
         * PCT_GE: greater then/equals PCT_LE: lower then/equals PCT_EQ: equals
         */
        PCT_GE, PCT_LE, PCT_EQ;

        @Override
        public String toString() {
            switch (this) {
            case PCT_GE:
                return ">= 0";
            case PCT_LE:
                return "<= 0";
            case PCT_EQ:
                return "= 0";
            default:
                return "??";
            }
        }
    }

    /**
     * Left side: a polynomial
     */
    private VarPolynomial varPolynomial;

    /**
     * Constraint type
     */
    private final PolynomialConstraintType type;

    /**
     * Is this a bound?
     */
    private boolean isBound;

    /**
     * Is this a upper bound?
     */
    private boolean isUpperBound;

    /**
     * Is this a lower bound?
     */
    private boolean isLowerBound;

    /**
     * If [this] is a bound, then we store the value.
     */
    private BigInteger bound;

    /**
     * If [this] is a bound, then we memorize the bounded variable.
     */
    private String boundedVariable;

    /**
     * Name generator.
     */
    private final FreshNameGenerator ng;

    /**
     * Constructor: Creates [vp] [pct] 0
     * @param vp a polynomial
     * @param pct the type
     * @param gen name generator
     */
    public PolynomialConstraint(final VarPolynomial vp, final PolynomialConstraintType pct, final FreshNameGenerator gen)
    {
        this.ng = gen;
        this.varPolynomial = vp;
        this.type = pct;
        this.divideByGGT();
        this.calcBoundInformation();
    }

    public Atom toAtom() {
        switch (this.type) {
        case PCT_EQ:
            return new Atom(this.varPolynomial, AtomType.ATOM_EQ, VarPolynomial.ZERO);
        case PCT_GE:
            return new Atom(this.varPolynomial, AtomType.ATOM_GE, VarPolynomial.ZERO);
        case PCT_LE:
            return new Atom(this.varPolynomial, AtomType.ATOM_LE, VarPolynomial.ZERO);
        default:
            assert false : "Default?!?";
            return null;
        }
    }

    /**
     * Creates a polynomial constraint: [left] [pct] [right]
     * @param left left polynomial
     * @param pct the constraint type
     * @param right right polynomial
     * @return a polynomial constraint
     */
    public static PolynomialConstraint create(
        final VarPolynomial left,
        final PolynomialConstraintType pct,
        final VarPolynomial right,
        final FreshNameGenerator gen)
    {
        return new PolynomialConstraint(left.minus(right), pct, gen);
    }

    /**
     * Returns the left side.
     * @return a polynomial
     */
    public VarPolynomial getPolynomial() {
        return this.varPolynomial;
    }

    /**
     * Return the type.
     * @return PolynomialConstraintType
     */
    public PolynomialConstraintType getType() {
        return this.type;
    }

    /**
     * Reset fields storing bound-information. This is use whenever we have to
     * recalculate the bound information. For example: x >= 0 is clearly a
     * bound, but after applying the substitution x/y+z we have y + z >= 0 which
     * is not a bound.
     */
    private void resetBoundInformation() {
        this.isBound = false;
        this.isLowerBound = false;
        this.isUpperBound = false;
        this.bound = null;
        this.boundedVariable = null;
    }

    /**
     * Calculates whether or not [this] is a bound and it also drains some
     * relevant information. For example -x + 17 <= 0 is bound, while x + y >= 0
     * is not a bound.
     */
    private void calcBoundInformation() {
        // 1. Is it possible, that [this] is a bound?
        final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials = this.varPolynomial.getVarMonomials();
        if (varMonomials.size() == 0 || varMonomials.size() > 2 || !this.varPolynomial.isConcrete()) {
            return;
        }

        // 2. Does it have exactly one variable?
        final Set<String> variables = this.varPolynomial.getVariables();
        if (variables.size() != 1) {
            return;
        }

        // 3. Is the variable at power 1?
        final String variable = variables.iterator().next();
        final SimplePolynomial factor = this.varPolynomial.getCoefficientPoly(variable);
        if (factor == null) {
            return;
        }

        // 4. Store information
        final SimplePolynomial constant = this.varPolynomial.getConstantPart();
        final BigInteger constantValue = constant.getNumericalAddend();
        if (variable != null) {
            this.isBound = true;
            this.boundedVariable = variable;
            switch (this.type) {
            case PCT_GE:
                this.isUpperBound = factor.equals(SimplePolynomial.MINUS_ONE);
                this.isLowerBound = !this.isUpperBound;
                this.bound = this.isUpperBound ? constantValue : constantValue.negate();
                break;
            case PCT_LE:
                this.isUpperBound = factor.equals(SimplePolynomial.ONE);
                this.isLowerBound = !this.isUpperBound;
                this.bound = this.isUpperBound ? constantValue.negate() : constantValue;
                break;
            case PCT_EQ:
                this.isUpperBound = true;
                this.isLowerBound = true;
                this.bound = factor.equals(SimplePolynomial.MINUS_ONE) ? constantValue : constantValue.negate();
                break;
            default:
                assert false;
            }
        }
    }

    /**
     * Returns true IFF [this] is a bound.
     * @return boolean
     */
    public boolean isBound() {
        return this.isBound;
    }

    /**
     * Returns true IFF [this] is a lower bound.
     * @return boolean
     */
    public boolean isLowerBound() {
        return this.isLowerBound;
    }

    /**
     * Returns true IFF [this] is a upper bound.
     * @return boolean
     */
    public boolean isUpperBound() {
        return this.isUpperBound;
    }

    /**
     * Returns the lower bound value. Example: x - 17 >= 0 -> 17
     * @return BigInteger
     */
    public BigInteger getLowerBoundValue() {
        if (!this.isLowerBound) {
            return null;
        }
        return this.bound;
    }

    /**
     * Returns the upper bound value. Example: x - 17 <= 0 -> 17
     * @return BigInteger
     */
    public BigInteger getUpperBoundValue() {
        if (!this.isUpperBound) {
            return null;
        }
        return this.bound;
    }

    /**
     * Returns the bounded variable. Example: x - 17 > 0 -> x
     * @return String
     */
    public String getBoundedVariable() {
        return this.boundedVariable;
    }

    /**
     * Returns all variables, that can be expressed by using the other
     * variables. Since we use integers, this is not always possible. Example: x
     * + 27y^17 yields x = w - 27y^17, where w is a fresh variable. Thus x can
     * be expressed.
     * @return set of expressible variables
     */
    public List<String> getExpressibleVariables() {
        final LinkedList<String> result = new LinkedList<String>();

        for (final Entry<IndefinitePart, SimplePolynomial> entry : this.varPolynomial.getVarMonomials().entrySet()) {
            final IndefinitePart indef = entry.getKey();
            final BigInteger coeff = entry.getValue().getNumericalAddend();
            // YAY! IndefinitePart.isIndefinite() is probably what I want here:
            if (indef.isIndefinite() && (coeff.equals(BigInteger.ONE) || coeff.equals(BigInteger.valueOf(-1)))) {
                result.add(indef.getExponents().keySet().iterator().next());
            }
        }
        return result;
    }

    /**
     * Expresses a variable. The constraint will be rewritten by substituting
     * the current polynomial for an fresh variable. The resulting equation is
     * transformed, so that [toExpress] is isolated. Example: x + 27y^17 - 42z
     * >= 0.expressVariable(x) yields (x =) w - 27y^17 + 42z and w >= 0.
     * @param toExpress variable to express. Caller has to ensure that toExpress
     * is expressible
     * @return Pair consisting of the expression and the new polynomial
     * constraint
     */
    public Pair<VarPolynomial, PolynomialConstraint> expressVariable(final String toExpress) {
        if (toExpress == null) {
            return null;
        }
        final String newVariable = this.ng.getFreshName("w", false);

        final IndefinitePart indefToExpress = IndefinitePart.create(toExpress, 1);
        final SimplePolynomial simplePoly = this.varPolynomial.getCoefficientPoly(indefToExpress);
        final BigInteger coeff = simplePoly.getNumericalAddend();
        boolean invert = false;
        if (coeff.equals(BigInteger.ONE)) {
            invert = true;
        } else if (!coeff.equals(BigInteger.valueOf(-1))) {
            // [toExpress] is not expressible.
            return null;
        }

        VarPolynomial resultPolynomial = VarPolynomial.createVariable(newVariable);
        resultPolynomial = invert ? resultPolynomial : resultPolynomial.negate();
        final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials = this.varPolynomial.getVarMonomials();
        final Map<IndefinitePart, SimplePolynomial> newVarMonomials =
            new LinkedHashMap<IndefinitePart, SimplePolynomial>(varMonomials);
        newVarMonomials.remove(indefToExpress);
        final VarPolynomial operand = VarPolynomial.create(ImmutableCreator.create(newVarMonomials));
        if (invert) {
            resultPolynomial = resultPolynomial.minus(operand);
        } else {
            resultPolynomial = resultPolynomial.plus(operand);
        }

        final PolynomialConstraint resultConstraint =
            new PolynomialConstraint(VarPolynomial.createVariable(newVariable), this.type, this.ng);

        return new Pair<VarPolynomial, PolynomialConstraint>(resultPolynomial, resultConstraint);
    }

    /**
     * Substitutes a variable for a polynomial.
     * @param toSubstitute variable to be substituted
     * @param toInsert polynomial to be inserted instead
     */
    public void substituteVariable(final String toSubstitute, final VarPolynomial toInsert) {
        // 1. Apply substitution:
        final Map<String, VarPolynomial> sub = new LinkedHashMap<String, VarPolynomial>(1);
        sub.put(toSubstitute, toInsert);
        this.varPolynomial = this.varPolynomial.substituteVariables(sub);

        // 2. Recalculate bound information:
        this.resetBoundInformation();
        this.calcBoundInformation();
    }

    /**
     * Divides by the GGT of the coefficients of non-constant monomials. This
     * method will also round the constant part in the correct way, i.e.
     * this.type = GE -> round down this.type = LE -> round up this.type = EQ ->
     * do not round (constant part must be divisible!) Example: 29 - 4y <= 0 ->
     * 8 - y <= 0
     * @return true IFF the polynomial was changed
     */
    private boolean divideByGGT() {
        if (!this.varPolynomial.isConcrete()) {
            return false;
        }

        final Set<SimplePolynomial> coeffs = this.varPolynomial.getCoefficientsOfVariables();
        final List<BigInteger> listOfRealCoeffs = new ArrayList<BigInteger>(coeffs.size());
        if (this.type.equals(PolynomialConstraintType.PCT_EQ)) {
            final SimplePolynomial constantPart = this.varPolynomial.getConstantPart();
            listOfRealCoeffs.add(constantPart.getNumericalAddend().abs());
        }
        for (final SimplePolynomial sp : coeffs) {
            if (sp.isConstant()) {
                final BigInteger coeff = sp.getNumericalAddend();
                listOfRealCoeffs.add(coeff.abs());
            } else {
                return false;
            }
        }
        if (listOfRealCoeffs.size() != 0) {
            BigInteger gcd = listOfRealCoeffs.get(0);
            for (int i = 1; i < listOfRealCoeffs.size(); i++) {
                gcd = gcd.gcd(listOfRealCoeffs.get(i));
            }
            if (gcd.equals(BigInteger.ZERO)) {
                return false;
            }
            final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials = this.varPolynomial.getVarMonomials();
            final Map<IndefinitePart, SimplePolynomial> newVarMonomials =
                new LinkedHashMap<IndefinitePart, SimplePolynomial>(varMonomials.size());
            for (final Entry<IndefinitePart, SimplePolynomial> entry : varMonomials.entrySet()) {
                final IndefinitePart key = entry.getKey();
                final SimplePolynomial simplePart = entry.getValue();
                final BigInteger simpleNumericalAddend = simplePart.getNumericalAddend();
                final BigInteger newCoefficient;

                if (key.isEmpty()) {
                    switch (this.type) {
                    case PCT_GE:
                        newCoefficient = ToolBox.divideAndRoundDown(simpleNumericalAddend, gcd);
                        break;
                    case PCT_LE:
                        newCoefficient = ToolBox.divideAndRoundUp(simpleNumericalAddend, gcd);
                        break;
                    default:
                        newCoefficient = simpleNumericalAddend.divide(gcd);
                        break;
                    }
                } else {
                    newCoefficient = simpleNumericalAddend.divide(gcd);
                }

                if (!newCoefficient.equals(BigInteger.ZERO)) {
                    final SimplePolynomial newCoeffSimplePoly = SimplePolynomial.create(newCoefficient);
                    newVarMonomials.put(key, newCoeffSimplePoly);
                }
            }
            if (Globals.DEBUG_MATTHIAS) {
                DebugLogger.getLogger("constraint").logln("Rounded " + this.toString());
            }
            this.varPolynomial = VarPolynomial.create(ImmutableCreator.create(newVarMonomials));
            if (Globals.DEBUG_MATTHIAS) {
                DebugLogger.getLogger("constraint").logln("to " + this.toString());
            }
            return true;
        }
        return false;
    }

    /**
     * Rewrite [this] to a integer-based SMT formula.
     * @return Formula\<SMTLIBTheoryAtom\>
     */
    public SMTLIBTheoryAtom toSMTTheoryAtom() {
        final SMTLIBIntValue value = ToolBox.rewriteVarPolynomialToSMTLIBIntValue(this.varPolynomial);
        final SMTLIBIntConstant zero = SMTLIBIntConstant.create(BigInteger.ZERO);
        switch (this.type) {
        case PCT_LE:
            return SMTLIBIntLE.create(value, zero);
        case PCT_GE:
            return SMTLIBIntGE.create(value, zero);
        case PCT_EQ:
            return SMTLIBIntEquals.create(value, zero);
        default:
            assert false;
            return null;
        }
    }

    /**
     * Rewrite [this] to a integer-based SMT formula, replacing non-linear
     * constraints by fresh variables and generates some useful constraints for
     * them.
     * @return SMTLIBTheoryAtom
     */
    public SMTLIBTheoryAtom toSMT(
        final List<Formula<SMTLIBTheoryAtom>> formulaList,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final FreshNameGenerator ng)
    {
        final SMTLIBIntValue value =
            ToolBox.rewriteVarPolynomialToSMTLIBIntValueLinear(this.varPolynomial, formulaList, factory, ng);
        final SMTLIBIntConstant zero = SMTLIBIntConstant.create(BigInteger.ZERO);
        final SMTLIBTheoryAtom preciousAtom;
        switch (this.type) {
        case PCT_LE:
            preciousAtom = SMTLIBIntLE.create(value, zero);
            break;
        case PCT_GE:
            preciousAtom = SMTLIBIntGE.create(value, zero);
            break;
        case PCT_EQ:
            preciousAtom = SMTLIBIntEquals.create(value, zero);
            break;
        default:
            assert false;
            preciousAtom = null;
        }
        return preciousAtom;
    }

    /**
     * Returns a representation of this as a term.
     * @param predefined some predefined map
     * @return Term
     */
    private TRSTerm toTerm(final IDPPredefinedMap predefined) {
        final SimplePolynomial constantPart = this.varPolynomial.getConstantPart();
        final TRSTerm leftSide = this.varPolynomial.minus(VarPolynomial.create(constantPart)).toTerm(predefined);
        final TRSTerm rightSide =
            predefined.getIntTerm(
                BigIntImmutable.create(constantPart.getNumericalAddend().negate()),
                DomainFactory.INTEGERS);

        switch (this.type) {
        case PCT_GE:
            return ToolBox.buildGe(leftSide, rightSide);
        case PCT_LE:
            return ToolBox.buildLe(leftSide, rightSide);
        case PCT_EQ:
            return ToolBox.buildEq(leftSide, rightSide);
        default:
            assert false : "Unknown constraint type: " + this.type;
            return null;
        }
    }

    /**
     * Returns a representation of this as a term.
     * @return Term
     */
    public TRSTerm toTerm() {
        return this.toTerm(ToolBox.PREDEFINED);
    }

    @Override
    public String toString() {
        return this.varPolynomial.toString() + " " + this.type.toString();
    }

    /**
     * Calculates whether or not "this" contradicts "other" in a trivial way.
     * For example: x >= 17 contradicts x <= 7. This method may return wrong
     * negative answers.
     * @param other the other polynomial constraint
     * @return boolean
     */
    public boolean contradicts(final PolynomialConstraint other) {
        if (other == null) {
            return false;
        } else {
            if (this.type == PolynomialConstraintType.PCT_EQ) {
                return (new PolynomialConstraint(this.varPolynomial, PolynomialConstraintType.PCT_GE, this.ng))
                    .contradicts(other)
                    || (new PolynomialConstraint(this.varPolynomial, PolynomialConstraintType.PCT_LE, this.ng))
                        .contradicts(other);
            }
            if (this.type == PolynomialConstraintType.PCT_LE) {
                return (new PolynomialConstraint(this.varPolynomial.negate(), PolynomialConstraintType.PCT_GE, this.ng))
                    .contradicts(other);
            }
            if (other.type == PolynomialConstraintType.PCT_LE || other.type == PolynomialConstraintType.PCT_EQ) {
                return other.contradicts(this);
            }

            // Now this.type = PCT_GE = other.type holds!
            final VarPolynomial sum = this.varPolynomial.plus(other.varPolynomial);
            if (sum.isConcrete() && sum.isConstant()) {
                return sum.getConstantPart().getNumericalAddend().compareTo(BigInteger.ZERO) < 0;
            } else {
                return false;
            }
        }
    }

    /**
     * Calculates whether or not "this" implies "other" in a trivial way. For
     * example: x >= 17 implies x >= 7. This method may return a wrong negative
     * answers.
     * @param other the other polynomial constraint
     * @return boolean
     */
    public boolean isStrongerThan(final PolynomialConstraint other) {
        if (other == null) {
            return false;
        }
        if (other.type == PolynomialConstraintType.PCT_EQ) {
            if (this.type == PolynomialConstraintType.PCT_EQ) {
                return this.varPolynomial.equals(other.varPolynomial);
            } else {
                return false;
            }
        }
        if (this.type == PolynomialConstraintType.PCT_EQ) {
            return ((new PolynomialConstraint(this.varPolynomial, PolynomialConstraintType.PCT_GE, this.ng))
                .isStrongerThan(other) || (new PolynomialConstraint(
                this.varPolynomial,
                PolynomialConstraintType.PCT_LE,
                this.ng)).isStrongerThan(other));
        }
        if (this.type == PolynomialConstraintType.PCT_LE) {
            return (new PolynomialConstraint(this.varPolynomial.negate(), PolynomialConstraintType.PCT_GE, this.ng))
                .isStrongerThan(other);
        }
        if (other.type == PolynomialConstraintType.PCT_LE) {
            return this.isStrongerThan(new PolynomialConstraint(
                other.varPolynomial.negate(),
                PolynomialConstraintType.PCT_GE,
                other.ng));
        }

        final VarPolynomial diff = other.varPolynomial.minus(this.varPolynomial);
        if (diff.isConcrete() && diff.isConstant()) {
            return diff.getConstantPart().getNumericalAddend().compareTo(BigInteger.ZERO) >= 0;
        }

        return false;
    }

    @Override
    public boolean equals(final Object that) {
        if (that == null || !(that instanceof PolynomialConstraint)) {
            return false;
        }
        final PolynomialConstraint other = (PolynomialConstraint) that;
        return this.type == other.type && this.varPolynomial.equals(other.varPolynomial);
    }

    @Override
    public int hashCode() {
        return this.type.hashCode() + 3 * this.varPolynomial.hashCode();
    }

    public FreshNameGenerator getNameGenerator() {
        return this.ng;
    }
}
