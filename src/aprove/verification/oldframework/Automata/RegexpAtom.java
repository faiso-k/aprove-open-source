package aprove.verification.oldframework.Automata;

/**
 * A regexp atom just represents a single letter.
 * @author cotto
 * @param <X> the alphabet
 */
public class RegexpAtom<X> extends Regexp<X> {

    /**
     * The letter stored in this atom.
     */
    private final X letter;

    /**
     * Create a regexp atom for the given letter.
     * @param l some letter
     */
    public RegexpAtom(final X l) {
        assert (l != null);
        this.letter = l;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result
                + ((this.letter == null) ? 0 : this.letter.hashCode());
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
        final RegexpAtom other = (RegexpAtom) obj;
        if (this.letter == null) {
            if (other.letter != null) {
                return false;
            }
        } else if (!this.letter.equals(other.letter)) {
            return false;
        }
        return true;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return this.letter.toString();
    }

    /**
     * @return the letter contained in this atomar regexp.
     */
    public X getLetter() {
        return this.letter;
    }
}
