package aprove.verification.oldframework.Automata;

import java.util.*;

/**
 * Concatenate two regular expressions: exp1.exp2
 * @author cotto
 * @param <X> the alphabet
 */
public final class RegexpConcat<X> extends Regexp<X> {
    /**
     * Concatenate a list of letters.
     * @param <X> the type of the letters.
     * @param word a word consisting of several letters.
     * @return the corresponding regexp.
     */
    public static <X> Regexp<X> create(final List<X> word) {
        Regexp<X> result = RegexpEpsilon.create();
        final Iterator<X> it = word.iterator();
        while (it.hasNext()) {
            final RegexpAtom<X> atom = new RegexpAtom<X>(it.next());
            result = result.concat(atom);
        }
        return result;
    }

    /**
     * @param <X> the alphabet
     * @param one some regular expression
     * @param two some regular expression
     * @return one.two
     */
    static <X> Regexp<X> create(final Regexp<X> one, final Regexp<X> two) {
        if (two instanceof RegexpEpsilon) {
            return one;
        } else if (two instanceof RegexpEmptyLanguage) {
            return two;
        }
        return new RegexpConcat<X>(one, two);
    }

    /**
     * The first subexpression.
     */
    private final Regexp<X> subOne;

    /**
     * The second subexpression.
     */
    private final Regexp<X> subTwo;

    /**
     * Just store the two subexpressions
     * @param one the first subexpression
     * @param two the second subexpression
     */
    private RegexpConcat(final Regexp<X> one, final Regexp<X> two) {
        this.subOne = one;
        this.subTwo = two;
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
        final RegexpConcat other = (RegexpConcat) obj;
        if (this.subOne == null) {
            if (other.subOne != null) {
                return false;
            }
        } else if (!this.subOne.equals(other.subOne)) {
            return false;
        }
        if (this.subTwo == null) {
            if (other.subTwo != null) {
                return false;
            }
        } else if (!this.subTwo.equals(other.subTwo)) {
            return false;
        }
        return true;
    }

    /**
     * @return the first subexpression
     */
    public Regexp<X> getSubOne() {
        return this.subOne;
    }

    /**
     * @return the second subexpression
     */
    public Regexp<X> getSubTwo() {
        return this.subTwo;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result
                + ((this.subOne == null) ? 0 : this.subOne.hashCode());
        result =
            prime * result
                + ((this.subTwo == null) ? 0 : this.subTwo.hashCode());
        return result;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return this.getSubOne().toString() + "." + this.getSubTwo().toString();
    }
}
