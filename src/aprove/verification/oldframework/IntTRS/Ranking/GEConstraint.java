package aprove.verification.oldframework.IntTRS.Ranking;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions.*;
import immutables.*;
/**
 * Represents a constraint, that something has to be greater than (or equal) a
 * constant. These constraint have the form polynomial >= constant where
 * denominator > 0 and polynomial is concrete and free of constants.
 * @author Matthias Hoelzel
 */
public final class GEConstraint implements Exportable {
    /**
     * The polynomial, which stand on the left side. Furthermore, it should be
     * concrete.
     */
    private final VarPolynomial poly;

    /** The constant, occurring at the right side. */
    private final BigInteger constant;

    /**
     * A constructor which assume to get valid values. To create constraints one
     * should call the corresponding create-method instead. However, it ensures
     * that the polynomial no longer has a constant part.
     * @param vp the polynomial occurring at the left side
     * @param c the constant occurring at the right side
     */
    private GEConstraint(final VarPolynomial vp, final BigInteger c) {
        final BigInteger constantPart = vp.getConstantPart().getNumericalAddend();

        this.poly = vp.minus(VarPolynomial.create(constantPart));
        this.constant = c.subtract(constantPart);
    }

    /**
     * Creates a valid GEConstraint.
     * @param vp the polynomial occurring at the left side
     * @param c the constant occurring at the right side
     * @return a valid GEConstraint
     */
    public static GEConstraint create(final VarPolynomial vp, final BigInteger c) {
        if (!vp.isConcrete()) {
            throw new UnsupportedOperationException("The polynomial must be concrete!");
        }
        BigInteger gcd = c.abs().max(BigInteger.ONE);
        for (final SimplePolynomial sp : vp.getAllCoefficients()) {
            gcd = gcd.gcd(sp.getNumericalAddend().abs());
        }
        assert gcd.compareTo(BigInteger.ZERO) > 0 : "Strange gcd calculated.";

        VarPolynomial resultPoly;
        BigInteger resultC;
        if (!gcd.equals(BigInteger.ONE)) {
            resultC = c.divide(gcd);
            final LinkedHashMap<IndefinitePart, SimplePolynomial> newPoly =
                new LinkedHashMap<>(vp.getVarMonomials().size());
            for (final Entry<IndefinitePart, SimplePolynomial> e : vp.getVarMonomials().entrySet()) {
                final SimplePolynomial simplePart = e.getValue();
                final IndefinitePart indefPart = e.getKey();
                newPoly.put(indefPart, SimplePolynomial.create(simplePart.getNumericalAddend().divide(gcd)));
            }
            resultPoly = VarPolynomial.create(ImmutableCreator.create(newPoly));
        } else {
            resultPoly = vp;
            resultC = c;
        }

        return new GEConstraint(
            resultPoly.minus(VarPolynomial.create(resultPoly.getConstantPart())),
            resultC.subtract(resultPoly.getConstantPart().getNumericalAddend()));
    }

    /**
     * @return a set of occurring variables.
     */
    public Set<String> getVariables() {
        return this.poly.getVariables();
    }

    /**
     * Returns the left side minus the right side, i.e. the difference
     * polynomial of x+y >= 2 is x+y-2.
     * @return VarPolynomial
     */
    public VarPolynomial getDiffPoly() {
        return this.poly.minus(VarPolynomial.create(this.constant));
    }

    /**
     * Getter for the polynomial.
     * @return VarPolynomial
     */
    public VarPolynomial getPoly() {
        return this.poly;
    }

    /**
     * Getter for the constant.
     * @return BigInteger
     */
    public BigInteger getConstant() {
        return this.constant;
    }

    /**
     * Returns a new GEConstraint with substituted variables.
     * @param substitution maps String to VarPolynomials
     * @return GEConstraint
     * @throws AbortionException can be aborted
     */
    public GEConstraint substitute(final Map<String, VarPolynomial> substitution, final Abortion aborter)
        throws AbortionException
    {
        assert substitution != null : "Substitution should not be null!";
        final VarPolynomial newPoly = this.poly.substituteVariables(substitution, aborter);
        return new GEConstraint(newPoly, this.constant);
    }

    /**
     * Returns true, if the degree of the polynomial is <= 1.
     * @return boolean
     */
    public boolean isLinear() {
        return this.poly.getDegree() <= 1;
    }

    /**
     * Rewrites this constraint to an SMTLIBRaTGE.
     * @return SMTLIBRATGE
     */
    public SMTLIBRatGE toSMTLIBRatGE() {
        final List<SMTLIBRatValue> ratMonomials = new LinkedList<>();
        for (final Entry<IndefinitePart, SimplePolynomial> entry : this.poly.getVarMonomials().entrySet()) {
            final IndefinitePart indef = entry.getKey();
            final SimplePolynomial simple = entry.getValue();
            final BigInteger addend = simple.getNumericalAddend();

            final SMTLIBRatValue ratVal = ToolBox.rewriteIndefinitePartToSMTLIBRatValue(indef);
            final SMTLIBRatConstant ratConst = SMTLIBRatConstant.create(addend);

            final List<SMTLIBRatValue> list = new LinkedList<>();
            list.add(ratVal);
            list.add(ratConst);
            final SMTLIBRatMult ratMult = SMTLIBRatMult.create(list);
            ratMonomials.add(ratMult);
        }

        final SMTLIBRatPlus ratPlus = SMTLIBRatPlus.create(ratMonomials);
        final SMTLIBRatConstant rightSide = SMTLIBRatConstant.create(this.constant);

        return SMTLIBRatGE.create(ratPlus, rightSide);
    }

    @Override
    public int hashCode() {
        return this.poly.hashCode() + this.constant.hashCode() * 2;
    }

    @Override
    public boolean equals(final Object other) {
        if (other == null || !(other instanceof GEConstraint)) {
            return false;
        }
        final GEConstraint otherConstraint = (GEConstraint) other;
        return this.poly.equals(otherConstraint.poly) && this.constant.equals(otherConstraint.constant);
    }

    @Override
    public String toString() {
        return this.poly.toString() + " >= " + this.constant.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        return this.poly.export(eu)
            + eu.escape(" ")
            + eu.geSign()
            + eu.escape(" ")
            + eu.escape(this.constant.toString());
    }

    /**
     * Constraints like 0 >= -1 are trivial. Thus, one may omit these trivial
     * constraints.
     * @return boolean
     */
    public boolean isTrivial() {
        return this.poly.isConcrete()
            && this.poly.isConstant()
            && this.poly.getConstantPart().getNumericalAddend().compareTo(this.constant) >= 0;
    }
}
