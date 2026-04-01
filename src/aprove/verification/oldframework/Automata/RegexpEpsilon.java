package aprove.verification.oldframework.Automata;

/**
 * A class (singleton) representing the empty word.
 * @author cotto
 * @param <X> the type of the letters
 */
public final class RegexpEpsilon<X> extends Regexp<X> {
    /**
     * The empty word.
     */
    @SuppressWarnings("unchecked")
    private static final RegexpEpsilon EPSILON = new RegexpEpsilon();

    /**
     * Create a letter representing the emtpy word.
     */
    private RegexpEpsilon() {
    }

    /**
     * @return epsilon.
     */
    @Override
    public Regexp<X> star() {
        return this;
    }

    /**
     * @param <X> the type of the letters.
     * @return the empty word.
     */
    @SuppressWarnings("unchecked")
    public static <X> Regexp<X> create() {
        return RegexpEpsilon.EPSILON;
    }

    /**
     * Concatenate the other regexp to this empty word, so just return the other
     * regexp.
     * @param other some regexp
     * @return the other regexp
     */
    @Override
    public Regexp<X> concat(final Regexp<X> other) {
        return other;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return "eps";
    }
}
