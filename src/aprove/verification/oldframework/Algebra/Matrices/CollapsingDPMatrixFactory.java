package aprove.verification.oldframework.Algebra.Matrices;


/**
 * This MatrixFactory implements all interpretations by Matrix multiplication,
 * but collapses DPs to a number.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public abstract class CollapsingDPMatrixFactory extends AbstractMatrixFactory {

    @Override
    public boolean supportsArbitraryQDP() {
        return false;
    }

    @Override
    public Matrix interpretArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

    }

    @Override
    public Matrix interpretDPArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        Matrix temp = ArgSymInterpretation.multiplyLeft(Interpretation);
        return ArgSymInterpretation.transpose().multiplyRight(temp);
    }

    @Override
    public Matrix interpretDP(Matrix DPSymInterpretation,
            Matrix ArgumentInterpretation) {

        return DPSymInterpretation.add(ArgumentInterpretation);

    }

    @Override
    public Matrix interpretFApp(Matrix FSymInterpretation,
            Matrix ArgumentInterpretation) {

        return FSymInterpretation.add(ArgumentInterpretation);
    }

}

