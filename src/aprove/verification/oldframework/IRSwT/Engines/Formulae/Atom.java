package aprove.verification.oldframework.IRSwT.Engines.Formulae;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;

/**
 * Represents an (arithmetical) atom of a formula. It consists of a left, a right
 * side and a comparison symbol (==, >=, <=, <, >).
 * @author Matthias Hoelzel
 */
public class Atom implements CheckableAndSMTExportable {
    /**
     * Possible types of atoms!
     */
    public enum AtomType {
        /**
         * ATOM_GE: greater or equal
         */
        ATOM_GE,
        /**
         * ATOM_EQ: equals
         */
        ATOM_EQ,
        /**
         * ATOM_GT: greater
         */
        ATOM_GT,
        /**
         * ATOM_LE: less or equal
         */
        ATOM_LE,
        /**
         * ATOM_LT: less
         */
        ATOM_LT;
    }

    /**
     * The polynomial at the left.
     */
    private final VarPolynomial leftPoly;

    /**
     * The polynomial at the right.
     */
    private final VarPolynomial rightPoly;

    /**
     * How do we compare these polynomials?
     */
    private final AtomType type;

    /**
     * Constructor!
     * @param left polynomial
     * @param atomType comparison type
     * @param right polynomial
     */
    public Atom(final VarPolynomial left, final AtomType atomType, final VarPolynomial right) {
        this.leftPoly = left;
        this.rightPoly = right;
        this.type = atomType;
    }

    /**
     * Getter for the left polynomial!
     * @return some VarPolynomial
     */
    public VarPolynomial getLeftPoly() {
        return this.leftPoly;
    }

    /**
     * Getter for the right polynomial!
     * @return some VarPolynomial
     */
    public VarPolynomial getRightPoly() {
        return this.rightPoly;
    }

    /**
     * Getter for the type!
     * @return the AtomType of this
     */
    public AtomType getType() {
        return this.type;
    }

    @Override
    public boolean check(final Map<String, PreciseRational> ass) {
        final PreciseRational left = Atom.evaluatePolynomial(this.leftPoly, ass);
        final PreciseRational right = Atom.evaluatePolynomial(this.rightPoly, ass);
        assert left != null && right != null : "Null?!";

        switch (this.type) {
        case ATOM_EQ:
            return left.equals(right);
        case ATOM_GE:
            return left.compareTo(right) >= 0;
        case ATOM_GT:
            return left.compareTo(right) > 0;
        case ATOM_LE:
            return left.compareTo(right) <= 0;
        case ATOM_LT:
            return left.compareTo(right) < 0;
        default:
            assert false : "Default case?";
            return false;
        }
    }

    /**
     * Evaluate a given polynomial w.r.t. to a given variable assignment.
     * @param vp some polynomial
     * @param ass some variable assignment
     * @return some arithmetical value
     */
    private static PreciseRational evaluatePolynomial(final VarPolynomial vp, final Map<String, PreciseRational> ass) {
        PreciseRational value = new PreciseRational(BigInteger.ZERO);
        for (final Entry<IndefinitePart, SimplePolynomial> e : vp.getVarMonomials().entrySet()) {
            value =
                value.add(Atom.evaluateIndefinitePart(e.getKey(), ass).multiply(
                    Atom.evaluateSimplePolynomial(e.getValue(), ass)));
        }
        return value;
    }

    /**
     * Evaluates a given indefinite part w.r.t. to a given variable assignment.
     * @param indef some indefinite part
     * @param ass some variable assignment
     * @return some arithmetical value
     */
    private static PreciseRational evaluateIndefinitePart(
        final IndefinitePart indef,
        final Map<String, PreciseRational> ass)
    {
        PreciseRational value = new PreciseRational(BigInteger.ONE);
        for (final Entry<String, Integer> e : indef.getExponents().entrySet()) {
            PreciseRational r = ass.get(e.getKey());
            if (r == null) {
                r = new PreciseRational(BigInteger.ZERO);
                if (Globals.DEBUG_MATTHIAS) {
                    System.err.println("null assignment!");
                }
            }
            value = value.multiply(r.power(e.getValue()));
        }
        return value;
    }

    /**
     * Evaluates a given simple polynomial w.r.t. to a given variable assignment.
     * @param simple some polynomial
     * @param ass some variable assignment
     * @return some arithmetical value
     */
    private static PreciseRational evaluateSimplePolynomial(
        final SimplePolynomial simple,
        final Map<String, PreciseRational> ass)
    {
        PreciseRational value = new PreciseRational(BigInteger.ZERO);
        for (final Entry<IndefinitePart, BigInteger> e : simple.getSimpleMonomials().entrySet()) {
            value = value.add(Atom.evaluateIndefinitePart(e.getKey(), ass).multiply(new PreciseRational(e.getValue())));
        }
        return value;
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBInt(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        final SMTLIBIntValue leftValue = this.leftPoly.toSMTLIB();
        final SMTLIBIntValue rightValue = this.rightPoly.toSMTLIB();
        switch (this.type) {
        case ATOM_EQ:
            return factory.buildTheoryAtom(SMTLIBIntEquals.create(leftValue, rightValue));
        case ATOM_GE:
            return factory.buildTheoryAtom(SMTLIBIntGE.create(leftValue, rightValue));
        case ATOM_GT:
            return factory.buildTheoryAtom(SMTLIBIntGT.create(leftValue, rightValue));
        case ATOM_LE:
            return factory.buildTheoryAtom(SMTLIBIntLE.create(leftValue, rightValue));
        case ATOM_LT:
            return factory.buildTheoryAtom(SMTLIBIntLT.create(leftValue, rightValue));
        default:
            assert false : "Default?!";
        }
        return null;
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBRat(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        final SMTLIBRatValue leftValue = ToolBox.rewriteVarPolynomalIntoSMTLIBRatValue(this.leftPoly);
        final SMTLIBRatValue rightValue = ToolBox.rewriteVarPolynomalIntoSMTLIBRatValue(this.rightPoly);
        switch (this.type) {
        case ATOM_EQ:
            return factory.buildTheoryAtom(SMTLIBRatEquals.create(leftValue, rightValue));
        case ATOM_GE:
            return factory.buildTheoryAtom(SMTLIBRatGE.create(leftValue, rightValue));
        case ATOM_GT:
            return factory.buildTheoryAtom(SMTLIBRatGT.create(leftValue, rightValue));
        case ATOM_LE:
            return factory.buildTheoryAtom(SMTLIBRatLE.create(leftValue, rightValue));
        case ATOM_LT:
            return factory.buildTheoryAtom(SMTLIBRatLT.create(leftValue, rightValue));
        default:
            assert false : "Default?!";
        }
        return null;
    }

    @Override
    public String toString() {
        String operator;
        switch (this.type) {
        case ATOM_EQ:
            operator = "=";
            break;
        case ATOM_GE:
            operator = ">=";
            break;
        case ATOM_GT:
            operator = ">";
            break;
        case ATOM_LE:
            operator = "<=";
            break;
        case ATOM_LT:
            operator = "<";
            break;
        default:
            operator = "?";
        }
        return this.leftPoly.toString() + operator + this.rightPoly.toString();
    }
}
