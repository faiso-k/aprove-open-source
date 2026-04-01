package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

/**
 *
 * @author MP
 */
public interface PolyTermSubstitution extends BasicTermSubstitution, BasicPolySubstitution {

    PolyTermSubstitution compose(PolyTermSubstitution sigma);
    PolyTermSubstitution polyTermCompose(BasicTermSubstitution sigma);
    @Override
    PolyTermSubstitution polyCompose(BasicPolySubstitution sigma);

//    boolean rememberEquals();

}