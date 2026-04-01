package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class NamedSymbol0<S extends Sort> extends Symbol0<S> implements NamedSymbol<S> {
    /**
     * Name of the symbol (e.g., variable name)
     */
    private final String name;

    /**
     * @param rv sort of this symbol
     * @param n name of the symbol
     */
    public NamedSymbol0(final S rv, final String n) {
        super(rv);
        this.name = n;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        result = prime * result + ((this.getType() == null) ? 0 : this.getType().hashCode());
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
        final NamedSymbol0 other = (NamedSymbol0) obj;
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        if (this.getType() == null) {
            if (other.getType() != null) {
                return false;
            }
        } else if (!this.getType().equals(other.getType())) {
            return false;
        }
        return true;
    }

    /** The user-defined name for this symbol. */
    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public String toString() {
        return this.name;
    }
}
