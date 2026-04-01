/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A range used in OrderPolyConstraints for the inner variables of the
 * polynomials. Each range is a list of intervals, e.g. {[0-5], [6-10]} where
 * the concrete meaning of this information is defined by the converter reading
 * the range. For integer ranges that where previously given as an integer i
 * (meaning 0..i) a valid range might be {[i-i]} which then is handled as
 * 0, 1, ..., i. Depending on the converter the range {[0-i]} might be more
 * logical and better, but this "proper" definition is not enforced.
 * For rational coefficients 2^8 the range {[0-0], [1/16-1/1]} might
 * be used to denote 0, 1/16, 1/8, ..., 1/2, 1/1. The same range could stand for
 * infinitely many values when used for some solver handling real numbers.
 *
 * The interval is given as a pair of elements defining the start and end of the
 * interval.
 * @author cotto
 * @param <C> The type of the coefficients used in the polynomials.
 */
public class OPCRange<C> {
    /**
     * The range.
     */
    private List<Pair<C, C>> list;

    /**
     * Create an empty range.
     */
    public OPCRange() {
        this.list = new ArrayList<Pair<C, C>>();
    }

    /**
     * Create a range with a single interval.
     * @param start The start of the interval.
     * @param end The end of the interval.
     */
    public OPCRange(final C start, final C end) {
        this.list = new ArrayList<Pair<C, C>>(1);
        this.extend(start, end);
    }

    /**
     * Extend the range by the given interval, defined by start and end.
     * @param start The start of the interval.
     * @param end The end of the interval.
     */
    public void extend(final C start, final C end) {
        Pair<C, C> pair = new Pair<C, C>(start, end);
        this.extend(pair);
    }

    /**
     * Extend the range by the given interval, defined by the pair of start
     * and end.
     * @param pair The pair with start and end.
     */
    public void extend(final Pair<C, C> pair) {
        this.list.add(pair);
    }

    /**
     * @return the list that represents the range.
     */
    public List<Pair<C, C>> getList() {
        return this.list;
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        return this.list.toString();
    }
}
