package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;

/**
 *
 * @author MP
 */
public class TermToPolyTermSubstitution extends AbstractTermToPolyTermSubstitution<BasicTermSubstitution, TermToPolyTermSubstitution> {

    public static PolyTermSubstitution create(final BasicTermSubstitution sigma, final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> polyInterpretation) {
        if (sigma instanceof PolyTermSubstitution) {
            return (PolyTermSubstitution) sigma;
        }
        return new TermToPolyTermSubstitution(sigma, predefinedMap, polyInterpretation);
    }

    protected TermToPolyTermSubstitution(final BasicTermSubstitution sigma,
            final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> interpretation) {
        super(sigma, predefinedMap, interpretation);
    }

    @Override
    protected TermToPolyTermSubstitution createNewInstance(final BasicTermSubstitution newSigma,
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<?> polyInterpretation) {
        return new TermToPolyTermSubstitution(newSigma, predefinedMap, polyInterpretation);
    }

    @Override
    public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

}
