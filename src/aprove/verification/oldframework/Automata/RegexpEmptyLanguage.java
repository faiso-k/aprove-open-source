package aprove.verification.oldframework.Automata;

/**
 * A class (singleton) representing the empty language.
 * @author cotto
 * @param <X> the type of the letters
 */
public final class RegexpEmptyLanguage<X> extends Regexp<X> {
    /**
     * The empty language.
     */
    @SuppressWarnings("unchecked")
    private static final RegexpEmptyLanguage EMPTYLANGUAGE =
        new RegexpEmptyLanguage();

    /**
     * Create a letter representing the emtpy language.
     */
    private RegexpEmptyLanguage() {
    }

    /**
     * @return empty language.
     */
    @Override
    public Regexp<X> star() {
        return RegexpEpsilon.create();
    }

    /**
     * @param <X> the type of the letters.
     * @return the empty language.
     */
    @SuppressWarnings("unchecked")
    public static <X> Regexp<X> create() {
        return RegexpEmptyLanguage.EMPTYLANGUAGE;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return "EMPTY LANGUAGE";
    }

    /**
     * Return the empty language.
     * @param other some regexp
     * @return this
     */
    @Override
    public Regexp<X> and(final Regexp<X> other) {
        return this;
    }

    /**
     * Return the empty language.
     * @param other some regexp
     * @return this
     */
    @Override
    public Regexp<X> concat(final Regexp<X> other) {
        return this;
    }

    /**
     * Return the other regexp.
     * @param other some regexp
     * @return other
     */
    @Override
    public Regexp<X> or(final Regexp<X> other) {
        return other;
    }
}
