package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

/**
 * @author MP
 */
public interface ImmutablePolyTermSubstitution extends BasicTermSubstitution,
        BasicPolySubstitution, ImmutableTermSubstitution,
        ImmutablePolySubstitution, PolyTermSubstitution {

    @Override
    ImmutablePolyTermSubstitution polyCompose(BasicPolySubstitution sigma);

    @Override
    ImmutablePolyTermSubstitution immutableTermCompose(BasicTermSubstitution sigma);

    @Override
    ImmutablePolyTermSubstitution replaceAllFunctionSymbols(FunctionSymbolReplacement sigma);

}
