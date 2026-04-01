package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.Itpf.*;

/**
 * Convenience class to represent possibly bisimilar ItpfITPs.
 * @author MP
 */
public class BisimItp implements BisimObject {

    /** The wrapped itp. */
    private final ItpfItp itp;

    /** @param itp itp to wrap. */
    public BisimItp(final ItpfItp itp) {
        this.itp = itp;
    }

    /** @return the wrapped itp. */
    public ItpfItp getItp() {
        return this.itp;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.itp.hashCode();
    }

    /** {@inheritDoc} */
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
        final BisimItp other = (BisimItp) obj;
        if (this.itp == null) {
            if (other.itp != null) {
                return false;
            }
        } else if (!this.itp.equals(other.itp)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "ITP: " + this.itp;
    }
}
