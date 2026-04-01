package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public interface ImmutableTermSubstitution extends BasicTermSubstitution, Immutable, XmlExportable {

    ImmutableTermSubstitution immutableTermCompose(BasicTermSubstitution sigma);
    ImmutableTermSubstitution replaceAllFunctionSymbols(FunctionSymbolReplacement sigma);

}
