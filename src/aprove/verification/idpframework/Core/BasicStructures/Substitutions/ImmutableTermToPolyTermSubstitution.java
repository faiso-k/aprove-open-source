package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;

/**
 *
 * @author MP
 */
public class ImmutableTermToPolyTermSubstitution extends AbstractTermToPolyTermSubstitution<ImmutableTermSubstitution, ImmutablePolyTermSubstitution> implements ImmutablePolyTermSubstitution {

    public static ImmutablePolyTermSubstitution create(final ImmutableTermSubstitution sigma, final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> polyInterpretation) {
        if (sigma instanceof ImmutablePolyTermSubstitution) {
            return (ImmutablePolyTermSubstitution) sigma;
        }
        return new ImmutableTermToPolyTermSubstitution(sigma, predefinedMap, polyInterpretation);
    }

    protected ImmutableTermToPolyTermSubstitution(final ImmutableTermSubstitution sigma,
            final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> interpretation) {
        super(sigma, predefinedMap, interpretation);
    }

    @Override
    protected ImmutablePolyTermSubstitution createNewInstance(final ImmutableTermSubstitution newSigma,
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<?> polyInterpretation) {
        return ImmutableTermToPolyTermSubstitution.create(newSigma, predefinedMap, polyInterpretation);
    }

    @Override
    public ImmutablePolyTermSubstitution replaceAllFunctionSymbols(final FunctionSymbolReplacement fsReplacement) {
        final ImmutableTermSubstitution newSigma = this.sigma.replaceAllFunctionSymbols(fsReplacement);
        if (newSigma != this.sigma) {
            return ImmutableTermToPolyTermSubstitution.create(newSigma, this.predefinedMap, this.polyInterpretation);
        } else {
            return this;
        }
    }

    @Override
    public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

    @Override
    public ImmutablePolyTermSubstitution immutableTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

    @Override
    public ImmutablePolySubstitution immutablePolyCompose(final BasicPolySubstitution sigma) {
        return this.polyCompose(sigma);
    }


    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        return null;
    }
}
