package aprove.verification.oldframework.Automata;

import java.util.*;

/**
 * Just a convenience class.
 * @author cotto
 * @param <X> the alphabet
 */
public abstract class RegexpNAry<X> extends Regexp<X> {
    /**
     * Store the subexpressions
     * @param args the subexpressions
     */
    public RegexpNAry(final Set<Regexp<X>> args) {
        this.subs = args;
    }

    /**
     * The subexpressions.
     */
    private final Set<Regexp<X>> subs;

    /**
     * Do not modify!
     * @return the subexpressions.
     */
    public Set<Regexp<X>> getSubs() {
        return this.subs;
    }

    /**
     * @param sym the symbol used for the operation
     * @return a nice string representation
     */
    public String toString(final String sym) {
        final Iterator<Regexp<X>> it = this.subs.iterator();
        final StringBuilder sb = new StringBuilder();
        sb.append("(");
        while (it.hasNext()) {
            sb.append(it.next().toString());
            if (it.hasNext()) {
                sb.append(sym);
            }
        }
        sb.append(")");
        return sb.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result + ((this.subs == null) ? 0 : this.subs.hashCode());
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
        final RegexpNAry other = (RegexpNAry) obj;
        if (this.subs == null) {
            if (other.subs != null) {
                return false;
            }
        } else if (!this.subs.equals(other.subs)) {
            return false;
        }
        return true;
    }
}
