package aprove.verification.idpframework.Polynomials.Interpretation;

import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 *
 * @author MP
 */
public final class PolyContextSwitchPair<C extends SemiRing<C>> implements Immutable {

    public final PolyBooleanVarSwitch<C> inc;
    public final PolyBooleanVarSwitch<C> dec;

    public PolyContextSwitchPair(final PolyBooleanVarSwitch<C> incSwitch, final PolyBooleanVarSwitch<C> decSwitch) {
        this.inc = incSwitch;
        this.dec = decSwitch;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.dec.hashCode();
        result = prime * result + this.inc.hashCode();
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final PolyContextSwitchPair<?> other = (PolyContextSwitchPair<?>) obj;
        return this.inc.equals(other.inc) && this.dec.equals(other.dec);
    }

    @Override
    public PolyContextSwitchPair<C> clone() {
        return new PolyContextSwitchPair<C>(this.inc.clone(), this.dec.clone());
    }

}
