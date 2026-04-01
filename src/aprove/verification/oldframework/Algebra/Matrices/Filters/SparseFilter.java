package aprove.verification.oldframework.Algebra.Matrices.Filters;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * SparseFilter - this filter allows restricting the maximum amount of coefficients which are nonzero to be limited.
 * @author kabasci
 * @version $Id$
 */
public class SparseFilter extends AbstractMatrixFilter implements MatrixFilter {

    private Map<String, Set<SimplePolynomial>> coefficientMap;
    private int max = 3;

    public void setMax(int max) {
        this.max = max;
    }

    public SparseFilter() {
        this.coefficientMap = new LinkedHashMap<String, Set<SimplePolynomial>>();
    }

    @Override
    public void tellCoefficient(String uid, SimplePolynomial coeff) {
        Set<SimplePolynomial> s = this.coefficientMap.get(uid);
        if (s == null) {
            s = new LinkedHashSet<SimplePolynomial>();
            this.coefficientMap.put(uid, s);
        }
        s.add(coeff);
    }

    @Override
    public Set<SimplePolyConstraint> getExtraConstraints() {

        LinkedHashSet<SimplePolyConstraint> res = new LinkedHashSet<SimplePolyConstraint>();

        for (Set<SimplePolynomial> s: this.coefficientMap.values()) {
            res.add (new SimplePolyConstraint (SimplePolynomial.create(this.max).minus(SimplePolynomial.plus(s)),  ConstraintType.GT));
        }

        return res;
    }

}

