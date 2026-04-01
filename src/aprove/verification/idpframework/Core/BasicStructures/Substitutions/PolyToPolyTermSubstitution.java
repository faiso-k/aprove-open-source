package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;

/**
 *
 * @author MP
 */
public class PolyToPolyTermSubstitution extends AbstractPolyToPolyTermSubstitution<BasicPolySubstitution, PolyToPolyTermSubstitution> {

    public static PolyTermSubstitution create(final BasicPolySubstitution sigma, final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> polyInterpretation) {
        if (sigma instanceof PolyTermSubstitution) {
            return (PolyTermSubstitution) sigma;
        }

        return new PolyToPolyTermSubstitution(sigma, predefinedMap, polyInterpretation);
    }

    protected PolyToPolyTermSubstitution(final BasicPolySubstitution sigma,
            final IDPPredefinedMap predefinedMap,
            final PolyInterpretation<?> polyInterpretation) {
        super(sigma, predefinedMap, polyInterpretation);
    }

    @Override
    protected PolyToPolyTermSubstitution createNewInstance(final BasicPolySubstitution newSigma,
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<?> polyInterpretation) {
        return new PolyToPolyTermSubstitution(newSigma, predefinedMap, polyInterpretation);
    }

    @Override
    public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }


}
