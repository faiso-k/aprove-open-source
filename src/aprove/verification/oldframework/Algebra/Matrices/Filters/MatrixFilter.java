package aprove.verification.oldframework.Algebra.Matrices.Filters;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 *
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public interface MatrixFilter {

    public enum Filtermode {
        ZERO,
        UNITYORZERO,
        FULLRANGE,
        ASSUMEZERO
    }

    public Filtermode filterCoefficient(int dimenson, int row, int col);

    // to be called after all processing is done, provides for extra constraints such as to limit density, sum of coefficients,...
    public Set<SimplePolyConstraint> getExtraConstraints();

    // after creation of the Matrix, pass the coefficient to the filter. Here, uid is a unique ID identifying the matrix (usually something like f{1}_0,1).
    public void tellCoefficient(String matrixUid, SimplePolynomial coeff);

}

