package aprove.verification.oldframework.Bytecode.Processors.PathLength;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * A MaxPolynomial should be considered as a something like
 * MAX(p_1, .. ,p_n) where p_i is a polynomial.
 * Therefore we store a MaxPolynomial in form of a set of polynomials.
 * Attention: we assume that the p_i are concrete polynomials.
 *
 * @author Matthias Hoelzel
 *
 */
public class MaxPolynomial {
    /**
     * See the p_i above.
     */
    private LinkedHashSet<VarPolynomial> polynomials;

    /**
     * Constructor
     * @param polys some polynomials
     */
    public MaxPolynomial(final VarPolynomial... polys) {
        this.polynomials = new LinkedHashSet<VarPolynomial>(polys.length);
        for (final VarPolynomial vp : polys) {
            this.polynomials.add(vp);
        }

        this.simplify();
    }

    /**
     * Constructor
     * @param polys some polynomials in a collection
     */
    public MaxPolynomial(final Collection<VarPolynomial> polys) {
        this.polynomials = new LinkedHashSet<VarPolynomial>(polys.size());
        this.polynomials.addAll(polys);

        this.simplify();
    }

    /**
     * Merges things like x + 5 and x + 17 into x + 17.
     */
    public void simplify() {
        final LinkedHashSet<VarPolynomial> result = new LinkedHashSet<VarPolynomial>(this.polynomials.size());
        for (final VarPolynomial a : this.polynomials) {
            boolean keep = true;
            for (final VarPolynomial b : this.polynomials) {
                if (a == b) {
                    continue;
                }
                final VarPolynomial diff = a.minus(b);
                if (diff.isConstant()) {
                    final SimplePolynomial simplePart = diff.getConstantPart();
                    final BigInteger bi = simplePart.getNumericalAddend();
                    if (bi.compareTo(BigInteger.ZERO) < 0) {
                        keep = false;
                        break;
                    }
                }
            }
            if (keep) {
                result.add(a);
            }
        }
        this.polynomials = result;
    }

    /**
     * Getter for this.polynomials.
     * @return a set of polynomials
     */
    public LinkedHashSet<VarPolynomial> getPolynomials() {
        return this.polynomials;
    }

    @Override
    public String toString() {
        final Iterator<VarPolynomial> iter = this.polynomials.iterator();
        final StringBuilder result = new StringBuilder("MAX(");
        while (iter.hasNext()) {
            final VarPolynomial next = iter.next();
            result.append(next);
            if (iter.hasNext()) {
                result.append(", ");
            }
        }
        result.append(")");
        return result.toString();
    }
}
