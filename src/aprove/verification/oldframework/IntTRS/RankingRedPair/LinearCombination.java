package aprove.verification.oldframework.IntTRS.RankingRedPair;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Consists two polynomials: VarPoly >= SimplePoly. We obtain such things, when
 * we multiply and add some GEConstraints.
 * @author Matthias Hoelzel
 */
public class LinearCombination {
    /** The first polynomial */
    private final VarPolynomial varPoly;

    /** The second polynomial */
    private final SimplePolynomial simplePoly;

    /** Set of coefficients occurring in this */
    private final LinkedHashSet<String> coefficients;

    /**
     * Constructor! Creates your new LinearCombination!
     * @param leftSide first polynomial
     * @param rightSide second polynomial
     */
    public LinearCombination(final VarPolynomial leftSide, final SimplePolynomial rightSide) {
        this.varPoly = leftSide;
        this.simplePoly = rightSide;

        final Set<String> coeffs1 = this.varPoly.getCoefficients();
        final Set<String> coeffs2 = this.simplePoly.getIndefinites();
        this.coefficients = new LinkedHashSet<>(coeffs1.size() + coeffs2.size());
        this.coefficients.addAll(coeffs1);
        this.coefficients.addAll(coeffs2);
    }

    /**
     * Returns the first polynomial.
     * @return VarPolynomial
     */
    public VarPolynomial getLeftSide() {
        return this.varPoly;
    }

    /**
     * Returns the second polynomial.
     * @return SimplePolynomial
     */
    public SimplePolynomial getRightSide() {
        return this.simplePoly;
    }

    /**
     * Returns the coefficients which occur in the polynomials.
     * @return LinkedHashSet of strings
     */
    public LinkedHashSet<String> getCoefficients() {
        return this.coefficients;
    }

    /**
     * Creates and returns a renamed version of this.
     * @param renaming maps the old names to the new ones
     * @return LinearCombination
     */
    public LinearCombination rename(final Map<String, String> renaming) {
        final LinkedHashMap<String, VarPolynomial> varPolySubstitution = new LinkedHashMap<>(renaming.size());
        final LinkedHashMap<String, SimplePolynomial> simplePolySubstitution = new LinkedHashMap<>(renaming.size());

        for (final Entry<String, String> e : renaming.entrySet()) {
            varPolySubstitution.put(e.getKey(), VarPolynomial.createVariable(e.getValue()));
            simplePolySubstitution.put(e.getKey(), SimplePolynomial.create(e.getValue()));
        }

        final VarPolynomial newVarPoly = this.varPoly.substituteVariables(varPolySubstitution);
        final SimplePolynomial newSimplePoly = this.simplePoly.substitute(simplePolySubstitution);

        return new LinearCombination(newVarPoly, newSimplePoly);
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.varPoly.toString());
        sb.append(" >= ");
        sb.append(this.simplePoly.toString());
        return sb.toString();
    }
}
