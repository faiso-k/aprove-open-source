package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;

/**
 * Represents a coefficient constraint.
 * @author Matthias Hoelzel
 */
public class CoefficientConstraint {
    /**
     * Enumeration of supported types.
     */
    public enum CoefficientConstraintType {
        /**
         * GE: Greater or equal EQ: Equals LE: Less or equal GT: Greater than
         * LT: Less than
         */
        GE_ZERO, EQ_ZERO, LE_ZERO, GT_ZERO, LT_ZERO;

        @Override
        public String toString() {
            switch (this) {
            case EQ_ZERO:
                return "= 0";
            case GE_ZERO:
                return ">= 0";
            case LE_ZERO:
                return "<= 0";
            case GT_ZERO:
                return "> 0";
            case LT_ZERO:
                return "< 0";
            default:
                return "??";
            }
        }
    }

    /**
     * The coefficient to be restricted
     */
    private final SimplePolynomial coefficient;

    /**
     * Constraint type
     */
    private final CoefficientConstraintType type;

    /**
     * Constructor
     * @param coeff Coefficient to be restricted
     * @param modus select >= 0 or == 0
     */
    public CoefficientConstraint(final SimplePolynomial coeff,
            final CoefficientConstraintType modus) {
        assert coeff != null && modus != null;
        this.coefficient = coeff;
        this.type = modus;
    }

    /**
     * Formulates this constraint as a SMTLIBIntTheoryAtom
     * @return SMTLIBTheoryAtom
     */
    public SMTLIBTheoryAtom toSMTLIBIntTheoryAtom() {
        // 1. Build value
        final SMTLIBIntValue value =
            ToolBox.rewriteSimplePolynomialToSMTLIBIntValue(this.coefficient);

        // 2. Build formula:
        switch (this.type) {
        case GE_ZERO:
            return SMTLIBIntGE.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        case EQ_ZERO:
            return SMTLIBIntEquals.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        case GT_ZERO:
            return SMTLIBIntGT.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        case LT_ZERO:
            return SMTLIBIntLT.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        case LE_ZERO:
            return SMTLIBIntLE.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        default:
            assert false;
            return null;
        }
    }

    /**
     * Formulates this constraint as a SMTLIBRatTheoryAtom
     * @return SMTLIBTheoryAtom
     */
    public SMTLIBTheoryAtom toSMTLIBRatTheoryAtom() {
        // 1. Build value
        final SMTLIBRatValue value =
            ToolBox.rewriteSimplePolynomialToSMTLIBRatValue(this.coefficient);

        // 2. Build formula:
        switch (this.type) {
        case GE_ZERO:
            return SMTLIBRatGE.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        case EQ_ZERO:
            return SMTLIBRatEquals.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        case GT_ZERO:
            return SMTLIBRatGT.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        case LT_ZERO:
            return SMTLIBRatLT.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        case LE_ZERO:
            return SMTLIBRatLE.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        default:
            assert false;
            return null;
        }
    }

    /**
     * If it returns true, then and only then [assignment] is a model of [this].
     * Please note, that [assignment] should assign every unknown coefficient of
     * [this].
     * @param assignment maps variables to integers
     * @return boolean
     */
    public boolean isSatisfied(final Map<String, BigInteger> assignment) {
        final SimplePolynomial value = this.coefficient.specialize(assignment);
        if (value.isConstant()) {
            switch (this.type) {
            case GE_ZERO:
                return value.getNumericalAddend().compareTo(BigInteger.ZERO) >= 0;
            case EQ_ZERO:
                return value.getNumericalAddend().compareTo(BigInteger.ZERO) == 0;
            case LE_ZERO:
                return value.getNumericalAddend().compareTo(BigInteger.ZERO) <= 0;
            case LT_ZERO:
                return value.getNumericalAddend().compareTo(BigInteger.ZERO) < 0;
            case GT_ZERO:
                return value.getNumericalAddend().compareTo(BigInteger.ZERO) > 0;
            default:
                assert false;
                return false;
            }
        }
        return false;
    }

    /**
     * If it returns true, then and only then [assignment] is a model of [this].
     * Please note, that [assignment] should assign every unknown coefficient of
     * [this].
     * @param assignment maps variables to rationals
     * @return boolean
     */
    public boolean isSatisfiedByRationalAssignment(final Map<String, PreciseRational> assignment) {
        final PreciseRational r =
            ToolBox.evaluateSimplePolynomial(this.coefficient, assignment);

        final PreciseRational zero = new PreciseRational(BigInteger.ZERO);

        switch (this.type) {
        case EQ_ZERO:
            return r.equals(zero);
        case GE_ZERO:
            return r.compareTo(zero) >= 0;
        case GT_ZERO:
            return r.compareTo(zero) > 0;
        case LE_ZERO:
            return r.compareTo(zero) <= 0;
        case LT_ZERO:
            return r.compareTo(zero) < 0;
        default:
            assert false : "Default ?!?";
        }
        return false;
    }

    @Override
    public String toString() {
        return this.coefficient.toString() + " " + this.type.toString();
    }
}
