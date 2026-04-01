package aprove.verification.oldframework.Algebra.Matrices.Filters;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * A basic matrix filter which other filters can inherit. Already provides nonfiltering functionality.
 * @author kabasci
 * @version $Id$
 */
public class AbstractMatrixFilter implements MatrixFilter {

    @Override
    public Filtermode filterCoefficient(int dimenson, int row, int col) {
        return Filtermode.FULLRANGE;
    }

    @Override
    public Set<SimplePolyConstraint> getExtraConstraints() {
        return new LinkedHashSet<SimplePolyConstraint>();
    }

    @Override
    public void tellCoefficient(String matrixUid, SimplePolynomial coeff) {
        // Thanks. But only needed in special filters.
    }

}

