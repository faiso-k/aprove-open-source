package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;

/**
 *
 * @author MP
 */
public class ImmutablePolyToPolyTermSubstitution extends AbstractPolyToPolyTermSubstitution<ImmutablePolySubstitution, ImmutablePolyToPolyTermSubstitution> {

    public static PolyTermSubstitution create(final ImmutablePolySubstitution sigma, final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> polyInterpretation) {
        if (sigma instanceof PolyTermSubstitution) {
            return (PolyTermSubstitution) sigma;
        }

        return new ImmutablePolyToPolyTermSubstitution(sigma, predefinedMap, polyInterpretation);
    }

    protected ImmutablePolyToPolyTermSubstitution(final ImmutablePolySubstitution sigma,
            final IDPPredefinedMap predefinedMap,
            final PolyInterpretation<?> polyInterpretation) {
        super(sigma, predefinedMap, polyInterpretation);
    }

    @Override
    protected ImmutablePolyToPolyTermSubstitution createNewInstance(final ImmutablePolySubstitution newSigma,
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<?> polyInterpretation) {
        return new ImmutablePolyToPolyTermSubstitution(newSigma, predefinedMap, polyInterpretation);
    }

    @Override
    public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

}
