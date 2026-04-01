package aprove.verification.diophantine;

import java.util.*;

import aprove.*;
import aprove.verification.diophantine.InfInt.*;
import immutables.*;

/**
 * Encapsulates intervals over the integers \cup {-\infty, \infty}
 * and basic operations on them. Intended for storing global knowledge
 * about the search space for SMT variables over the integers.
 *
 * @author Carsten Fuhs
 */
public class SearchBounds implements Immutable {

    public static final SearchBounds UNLIMITED
        = new SearchBounds(InfInt.MINUS_INFINITY, InfInt.PLUS_INFINITY);

    private final InfInt lowerBound;
    private final InfInt upperBound;

    private SearchBounds(InfInt lowerBound, InfInt upperBound) {
        if (Globals.useAssertions) {
            assert lowerBound != null;
            assert upperBound != null;
            assert lowerBound.compareTo(upperBound) < 0
                : lowerBound + " is not smaller than " + upperBound + '!';
        }
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
    }

    /**
     * Requires that lowerBound represents a strictly smaller value
     * than upperBound.
     *
     * @param lowerBound - non-null
     * @param upperBound - non-null
     * @return a new SearchBounds object encapsulating lowerBound
     *  and upperBound
     */
    public static SearchBounds create(InfInt lowerBound, InfInt upperBound) {
        return new SearchBounds(lowerBound, upperBound);
    }

    /**
     * Let this = [a1, b1].
     * @param other - [a2, b2]
     * @return a new interval [a1+a2, b1+b2], where adding infinite values
     *  again yields infinite values
     */
    public SearchBounds plus(SearchBounds other) {
        return this.plus(other.lowerBound, other.upperBound);
    }

    /**
     * Let this = [a1, b1].
     * @param otherLowerBound
     * @param otherUpperBound
     * @return a new interval [a1+otherLowerBound, b1+otherUpperBound],
     *  where adding infinite values again yields infinite values
     */
    private SearchBounds plus(InfInt otherLowerBound, InfInt otherUpperBound) {
        final InfInt newLowerBound = this.lowerBound.plus(otherLowerBound);
        if (newLowerBound == null) {
            return SearchBounds.UNLIMITED;
        }
        final InfInt newUpperBound = this.upperBound.plus(otherUpperBound);
        if (newUpperBound == null) {
            return SearchBounds.UNLIMITED;
        }
        SearchBounds res = SearchBounds.create(newLowerBound, newUpperBound);
        return res;
    }

    /**
     * Let this = [a1, b1].
     * @param other - [a2, b2]
     * @return a new interval [a1-b2, b1-a2], where adding infinite values
     *  again yields infinite values
     */
    public SearchBounds minus(final SearchBounds other) {
        final InfInt negatedOtherLower = other.upperBound.negate();
        final InfInt negatedOtherUpper = other.lowerBound.negate();
        return this.plus(negatedOtherLower, negatedOtherUpper);
    }

    /**
     * Let this = [a1, b1].
     * @param other - [a2, b2]
     * @return a new interval [a1+a2, b1+b2], where adding infinite values
     *  again yields infinite values
     */
    public SearchBounds times(final SearchBounds other) {
        // sort things out automatically (further case analysis
        // based on signum and infiniteness of the boundaries
        // might still save a few CPU cycles)
        final List<InfInt> extremalValues = new ArrayList<InfInt>(4);
        final InfInt b1 = this.lowerBound.times(other.lowerBound);
        if (b1 != null) { // beware of 0 * - \infty
            extremalValues.add(b1);
        }
        final InfInt b2 = this.lowerBound.times(other.upperBound);
        if (b2 != null) {
            extremalValues.add(b2);
        }
        final InfInt b3 = this.upperBound.times(other.lowerBound);
        if (b3 != null) {
            extremalValues.add(b3);
        }
        final InfInt b4 = this.upperBound.times(other.upperBound);
        if (b4 != null) {
            extremalValues.add(b4);
        }
        if (Globals.useAssertions) {
            assert extremalValues.size() >= 2 : "Multiplying boundaries of "
                    + this + " and " + other + " gives only "
                    + extremalValues + '!';
        }
        Collections.sort(extremalValues);
        final InfInt newLowerBound = extremalValues.get(0);
        final InfInt newUpperBound = extremalValues.get(extremalValues.size()-1);
        final SearchBounds res = SearchBounds.create(newLowerBound, newUpperBound);
        return res;
    }

    /**
     * Let this = [a, b].
     * @return [-b, -a]
     */
    public SearchBounds negate() {
        return SearchBounds.create(this.upperBound.negate(), this.lowerBound.negate());
    }

    /**
     * Let this = [a1, b1].
     *
     * @param other - [a2, b2]
     * @return a new interval [max(a1,a2), min(b1,b2)],
     *  null in case the lower bound would not be smaller than the upper bound
     */
    public SearchBounds intersect(SearchBounds other) {
        final InfInt newLowerBound = this.lowerBound.max(other.lowerBound);
        final InfInt newUpperBound = this.upperBound.min(other.upperBound);
        if (newLowerBound.compareTo(newUpperBound) >= 0) {
            return null;
        }
        return SearchBounds.create(newLowerBound, newUpperBound);
    }

    /**
     * @return whether this represents a finite interval (i.e., both the lower
     *  and the upper bound are finite numbers)
     */
    public boolean isFinite() {
        return this.lowerBound.getType() == InfIntType.FINITE
            && this.upperBound.getType() == InfIntType.FINITE;
    }

    /**
     * @return the lowerBound
     */
    public InfInt getLowerBound() {
        return this.lowerBound;
    }

    /**
     * @return the upperBound
     */
    public InfInt getUpperBound() {
        return this.upperBound;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.lowerBound == null) ? 0 : this.lowerBound.hashCode());
        result = prime * result
                + ((this.upperBound == null) ? 0 : this.upperBound.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        SearchBounds other = (SearchBounds) obj;
        if (this.lowerBound == null) {
            if (other.lowerBound != null) {
                return false;
            }
        }
        else if (!this.lowerBound.equals(other.lowerBound)) {
            return false;
        }
        if (this.upperBound == null) {
            if (other.upperBound != null) {
                return false;
            }
        }
        else if (!this.upperBound.equals(other.upperBound)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return '[' + this.lowerBound.toString() + ", "
                   + this.upperBound.toString() + ']';
    }
}
