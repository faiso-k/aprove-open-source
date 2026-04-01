package aprove.verification.oldframework.Automata;

/**
 * A regular expression with a kleene star wrapped around it.
 * @author cotto
 * @param <X> the alphabet.
 */
public final class RegexpStar<X> extends Regexp<X> {
    /**
     * The subexpression.
     */
    private final Regexp<X> sub;

    /**
     * Create a new regexp param*
     * @param param some regexp
     */
    private RegexpStar(final Regexp<X> param) {
        this.sub = param;
    }

    /**
     * @return the subexpression
     */
    public Regexp<X> getSub() {
        return this.sub;
    }

    /**
     * @param <X> the alphabet
     * @param sub some regexp
     * @return sub*
     */
    static <X> Regexp<X> create(final Regexp<X> sub) {
        if (sub instanceof RegexpStar || sub instanceof RegexpEpsilon) {
            return sub;
        }
        return new RegexpStar<X>(sub);
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return "(" + this.sub.toString() + ")*";
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result + ((this.sub == null) ? 0 : this.sub.hashCode());
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
        final RegexpStar other = (RegexpStar) obj;
        if (this.sub == null) {
            if (other.sub != null) {
                return false;
            }
        } else if (!this.sub.equals(other.sub)) {
            return false;
        }
        return true;
    }

}
