package aprove.verification.oldframework.Algebra.Matrices;



/**
 * This MatrixFactory implements all interpretations by Matrix multiplication
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public abstract class BasicMatrixFactory extends AbstractMatrixFactory {


    @Override
    public Matrix interpretArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

    }

    @Override
    public Matrix interpretDPArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

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

