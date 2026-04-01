package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import immutables.*;

/**
 *
 * @author MP
 */
public interface ImmutablePolySubstitution extends BasicPolySubstitution, Immutable {

    ImmutablePolySubstitution immutablePolyCompose(BasicPolySubstitution sigma);

}
