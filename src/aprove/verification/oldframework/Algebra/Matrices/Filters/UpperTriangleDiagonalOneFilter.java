package aprove.verification.oldframework.Algebra.Matrices.Filters;

/**
 * This Matrixfilter filters the lower triangle minus main diagonal
 * @author Patrick Kabasci
 * @version $Id$
 */
public class UpperTriangleDiagonalOneFilter extends AbstractMatrixFilter implements MatrixFilter {

    @Override
    public Filtermode filterCoefficient(int dimenson, int row, int col) {
        return (row > col) ? Filtermode.ZERO : (row == col) ? Filtermode.UNITYORZERO : Filtermode.FULLRANGE;
    }

}

