package aprove.verification.idpframework.Polynomials.Interpretation;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class VFISet<C extends SemiRing<C>> implements Immutable {

    public final Itpf incCondition;
    public final Itpf decCondition;
    public final ItpfBoolPolyVar<C> inc;
    public final ItpfBoolPolyVar<C> dec;
    private final ImmutablePair<Itpf, Itpf> activeSwitchPair;

    public VFISet(final ItpfBoolPolyVar<C> incVar, final Itpf incCondition,
            final ItpfBoolPolyVar<C> decVar,
            final Itpf decCondition) {
        this.inc = incVar;
        this.incCondition = incCondition;
        this.dec = decVar;
        this.decCondition = decCondition;
        this.activeSwitchPair = new ImmutablePair<Itpf, Itpf>(incCondition, decCondition);
    }

    public ImmutablePair<Itpf, Itpf> getActiveSwitchPair() {
        return this.activeSwitchPair;
    }

}
