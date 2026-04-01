package aprove.verification.idpframework.Processors.Filters.Bisimulation;

import aprove.verification.idpframework.Core.BasicStructures.*;

/**
 * Convenience class to represent possibly bisimilar function symbols.
 * @author MP
 */
public class BisimFS implements BisimObject {
    /** The wrapped function symbol. */
    private final IFunctionSymbol<?> fs;

    /** @param f Function symbol to wrap. */
    public BisimFS(final IFunctionSymbol<?> f) {
        this.fs = f;
    }

    /** @return the wrapped function symbol. */
    public IFunctionSymbol<?> getFs() {
        return this.fs;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.fs.hashCode();
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
        final BisimFS other = (BisimFS) obj;
        if (this.fs == null) {
            if (other.fs != null) {
                return false;
            }
        } else if (!this.fs.equals(other.fs)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return "FS: " + this.fs;
    }
}