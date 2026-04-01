package aprove.verification.oldframework.Algebra.Matrices.Filters;

/**
 * This Matrixfilter filters everything but the diagonal, the diagonal right to it and the first row.
 * @author Patrick Kabasci
 * @version $Id$
 */
public class ScissorFilter extends AbstractMatrixFilter implements MatrixFilter {

    @Override
    public Filtermode filterCoefficient(int dimenson, int row, int col) {
        return ((row == col) || (row + 1 == col)) ? Filtermode.FULLRANGE : Filtermode.ZERO;
    }


}

