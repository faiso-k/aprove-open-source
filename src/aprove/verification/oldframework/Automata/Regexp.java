package aprove.verification.oldframework.Automata;

import java.util.*;

/**
 * A regular expression in the sense of automata, monoids, ... in contrast to
 * those in programming languages like Perl.
 * @author cotto
 * @param <X> the alphabet.
 */
public abstract class Regexp<X> {
    /**
     * Put a Kleene star around this regexp.
     * @return this*
     */
    public Regexp<X> star() {
        return RegexpStar.create(this);
    }

    /**
     * Create an or expression of this and the given regexp.
     * @param other some regexp
     * @return this | other
     */
    public Regexp<X> or(final Regexp<X> other) {
        final Set<Regexp<X>> set = new LinkedHashSet<Regexp<X>>(2);
        set.add(this);
        set.add(other);
        return RegexpOr.create(set);
    }

    /**
     * Concatenate the given regexp to this.
     * @param other some regexp
     * @return this.other
     */
    public Regexp<X> concat(final Regexp<X> other) {
        return RegexpConcat.create(this, other);
    }

    /**
     * Create an and expression of this and the given regexp.
     * @param other some regexp
     * @return this & other
     */
    public Regexp<X> and(final Regexp<X> other) {
        final Set<Regexp<X>> set = new LinkedHashSet<Regexp<X>>(2);
        set.add(this);
        set.add(other);
        return RegexpAnd.create(set);
    }

    /**
     * @param word a list of letters
     * @return true iff the language defined by this regexp contains the given
     * word.
     */
    public boolean includes(final List<X> word) {
        final Regexp<X> wordRegexp = RegexpConcat.create(word);
        return this.includesAll(wordRegexp);
    }

    /**
     * @param regexp some regular expression
     * @return true iff the language defined by this regexp contains all words
     * defined by the given regexp.
     */
    public boolean includesAll(final Regexp<X> regexp) {
        final Automaton<Object, X> a1 = Automaton.create(this);
        final Automaton<Object, X> a2 = Automaton.create(regexp);
        return a1.containsAll(a2);
    }
}
