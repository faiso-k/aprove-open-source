package aprove.verification.oldframework.Algebra.Matrices.Filters;


/**
 * This Matrixfilter assumes that indeed a matrix of a smaller dimension can allready solve the problem.
 * @author Patrick Kabasci
 * @version $Id$
 */
public class AssumeOneSmallerFilter extends AbstractMatrixFilter implements MatrixFilter {

    @Override
    public Filtermode filterCoefficient(int dimension, int row, int col) {

        return (row == dimension - 1 || col == dimension - 1) ? Filtermode.ASSUMEZERO : Filtermode.FULLRANGE;
    }

}
