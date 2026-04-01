package aprove.verification.idpframework.Polynomials.Interpretation;

import aprove.verification.idpframework.Core.Itpf.*;

/**
 *
 * @author MP
 */
public class ActiveSwitch {

    public final ItpfLogVar dec;
    public final ItpfLogVar inc;

    public ActiveSwitch(final ItpfLogVar inc, final ItpfLogVar dec) {
        this.inc = inc;
        this.dec = dec;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.inc.hashCode();
        result = prime * result + this.dec.hashCode();
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
        final ActiveSwitch other = (ActiveSwitch) obj;
        return this.inc.equals(other.inc) && this.dec.equals(other.dec);
    }
}
