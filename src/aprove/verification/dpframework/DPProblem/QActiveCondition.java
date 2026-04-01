package aprove.verification.dpframework.DPProblem;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class represents activation conditions on
 * when a certain rule is usable. In fact, it represents
 * arbitrary non-negative boolean formulas over
 * predicates functionSymbol/position.
 *
 * The returned set (and internal state) is a set of
 * set of pairs of function symbols and integers.
 * It represents the disjunction of the conjunction of
 * the pairs, e.g.
 * { {f/0, f/3}, {g/1, f/2}, {g/2} } represents the formula
 * (f/0 and f/3) or (g/1 and f/2) or g/2.
 * Note that the returned sets
 * (and in the internal representation) there are no
 * redundancies, e.g. { {f/1, f/2}, {f/1} } would be
 * simplified to {{f/1}}.
 *
 * Do not modify any of the sets returned by any public
 * method until it is explicitly stated.
 *
 * Note that the formula TRUE is represented by one
 * unique object to be able to do fast checks with
 * == instead of equals.
 *
 * @author thiemann
 */
public class QActiveCondition implements Immutable {

    public static enum Direction {
        Normal, Reversed, Both, None
    };

    public static enum Dependence {
        None, Incr, Decr, Wild
    };

    public interface ExtendedAfs {
        Dependence filterPosition(FunctionSymbol f, int i);
    }

    public interface Afs {
        YNM filterPosition(FunctionSymbol f, int i);
    }

    // the set of set of (f/i) means
    // whenever orCondition contains one set andConds where
    // all (f/i) are present in the filtering,
    // then the Condition is satisfied
    private final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> orCondition;

    private int hash;
    private final boolean hashValid;

    private static boolean firstBuild = true;

    private QActiveCondition(final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> orCondition) {
        this.orCondition = orCondition;
        this.hash = 0;
        this.hashValid = false;
        if (Globals.useAssertions) {
            if (QActiveCondition.firstBuild) { // the first build is TRUE
                QActiveCondition.firstBuild = false;
            } else {
                // later there must not be build an equivalent QActiveCondition to TRUE.
                assert (orCondition.size() != 1 || !orCondition.iterator().next().isEmpty());
            }
        }
    }

    @Override
    public String toString() {
        boolean firstOr = true;
        String res = "";
        for (final SortedSet<Pair<FunctionSymbol, Integer>> andSet : this.orCondition) {
            boolean firstAnd = true;
            String sub = "";
            for (final Pair<FunctionSymbol, Integer> cond : andSet) {
                if (firstAnd) {
                    firstAnd = false;
                    sub += "{";
                } else {
                    sub += ", ";
                }
                sub += cond.x.getName() + "/" + (cond.y + 1);
            }
            if (firstAnd) {
                sub = "TRUE";
            } else {
                sub += "}";
            }
            if (firstOr) {
                firstOr = false;
            } else {
                res += " or ";
            }
            res += sub;
        }
        if (firstOr) {
            res = "FALSE";
        }
        return res;
    }

    /**
     * computes this and formula
     * @param formula
     * @return
     */
    public QActiveCondition and(final QActiveCondition formula) {
        if (this == QActiveCondition.TRUE) {
            return formula;
        } else if (formula == QActiveCondition.TRUE) {
            return this;
        } else {
            SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> oneOr = this.orCondition;
            SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> otherOr = formula.orCondition;
            if (oneOr.size() > otherOr.size()) {
                oneOr = otherOr;
                otherOr = this.orCondition;
            }
            SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> res;
            if (oneOr.size() == 0) {
                res = new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
            } else {
                final Iterator<SortedSet<Pair<FunctionSymbol, Integer>>> it = oneOr.iterator();
                SortedSet<Pair<FunctionSymbol, Integer>> conjunction = it.next();
                res = QActiveCondition.and(otherOr, conjunction);

                while (it.hasNext()) {
                    conjunction = it.next();
                    res = QActiveCondition.union(res, QActiveCondition.and(otherOr, conjunction));
                }
            }
            return new QActiveCondition(res);
        }
    }

    /**
     * computes "formula and conjunction"
     * @param formula
     * @param conjunction
     */
    private static SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> and(final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> formula,
        final SortedSet<Pair<FunctionSymbol, Integer>> conjunction) {
        if (conjunction.isEmpty()) {
            return formula;
        }
        if (conjunction.size() == 1) {
            return QActiveCondition.and(formula, conjunction.iterator().next());
        }
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> newOrCondition =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> newOrConditionMaybe =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        for (final SortedSet<Pair<FunctionSymbol, Integer>> andCond : formula) {
            final SortedSet<Pair<FunctionSymbol, Integer>> newAndCond = new TreeSet<Pair<FunctionSymbol, Integer>>(andCond);
            newAndCond.addAll(conjunction);
            newOrConditionMaybe.add(newAndCond);
        }
        QActiveCondition.maybeInsertForUnion(newOrCondition, newOrConditionMaybe);
        return newOrCondition;
    }

    /**
     * computes "this and f/position"
     * @param f
     * @param position
     */
    public QActiveCondition and(final FunctionSymbol f, final int position) {
        final Pair<FunctionSymbol, Integer> newCond = new Pair<FunctionSymbol, Integer>(f, position);
        return new QActiveCondition(QActiveCondition.and(this.orCondition, newCond));
    }

    /**
     * computes "formula and newCond"
     * @param formula
     * @param newCond the condition f/i to be added
     */
    private static SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> and(final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> formula,
        final Pair<FunctionSymbol, Integer> newCond) {
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> newOrCondition =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> newOrConditionMaybe =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        for (final SortedSet<Pair<FunctionSymbol, Integer>> andCond : formula) {
            if (andCond.contains(newCond)) {
                newOrCondition.add(andCond);
            } else {
                final SortedSet<Pair<FunctionSymbol, Integer>> newAndCond =
                    new TreeSet<Pair<FunctionSymbol, Integer>>(andCond);
                newAndCond.add(newCond);
                newOrConditionMaybe.add(newAndCond);
            }
        }
        QActiveCondition.maybeInsertForUnion(newOrCondition, newOrConditionMaybe);
        return newOrCondition;
    }

    /**
     * logically computes the union of the two sets into orig,
     * however, if some set in toInsert is a superset of some set in orig,
     * then it will not be inserted.
     * This can be used for simplification if the toInsert sets are
     * disjoint and can never be subsets of some set in orig.
     * Note the orig set will be modified on top level as required set
     * effect, but also the toInsert set will be modified on top level!
     * @param orig
     * @param toInsert
     */
    private static void maybeInsertForUnion(final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> orig,
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> toInsert) {

        final Iterator<SortedSet<Pair<FunctionSymbol, Integer>>> toInsertIterator = toInsert.iterator();

        nextToInsert: while (toInsertIterator.hasNext()) {
            final SortedSet<Pair<FunctionSymbol, Integer>> insert = toInsertIterator.next();
            final int size = insert.size();
            for (final SortedSet<Pair<FunctionSymbol, Integer>> origSet : orig) {
                if (size >= origSet.size() && QActiveCondition.isSuperSetOf(insert, origSet) >= 0) {
                    toInsertIterator.remove();
                    continue nextToInsert;
                }
            }
        }

        orig.addAll(toInsert);
    }

    /**
     * checks "as superSet bs".
     * @param <T>
     * @param as
     * @param bs
     * @return 0 if as = bs, 1 if as proper superset bs, -1 if not as superset bs
     */
    private static final <T> int isSuperSetOf(final SortedSet<T> as, final SortedSet<T> bs) {
        final Comparator<? super T> comp = as.comparator();
        final Iterator<T> asIt = as.iterator();
        final Iterator<T> bsIt = bs.iterator();
        boolean proper = false;
        next_b: while (bsIt.hasNext()) {
            final T b = bsIt.next();
            while (asIt.hasNext()) {
                final T a = asIt.next();
                final int c = comp.compare(a, b);
                if (c > 0) {
                    return -1;
                }
                if (c == 0) {
                    continue next_b;
                } else {
                    proper = true;
                }
            }
            return -1;
        }
        if (asIt.hasNext()) {
            proper = true;
        }
        return proper ? 1 : 0;
    }

    private static final Comparator<Pair<FunctionSymbol, Integer>> PAIR_COMPARATOR =
        new Comparator<Pair<FunctionSymbol, Integer>>() {

            @Override
            public int compare(final Pair<FunctionSymbol, Integer> o1, final Pair<FunctionSymbol, Integer> o2) {
                final int compare = o1.x.compareTo(o2.x);
                if (compare != 0) {
                    return compare;
                }
                return o1.y.compareTo(o2.y);
            }

        };

    private static final Comparator<SortedSet<Pair<FunctionSymbol, Integer>>> AND_COMPARATOR =
        new Comparator<SortedSet<Pair<FunctionSymbol, Integer>>>() {

            @Override
            public int compare(final SortedSet<Pair<FunctionSymbol, Integer>> o1, final SortedSet<Pair<FunctionSymbol, Integer>> o2) {
                final int s1 = o1.size();
                final int s2 = o2.size();
                if (s1 < s2) {
                    return -2;
                } else if (s1 > s2) {
                    return 2;
                } else {
                    final Iterator<Pair<FunctionSymbol, Integer>> o1It = o1.iterator();
                    final Iterator<Pair<FunctionSymbol, Integer>> o2It = o2.iterator();
                    int comp = 0;
                    while (comp == 0 && o1It.hasNext()) {
                        comp = QActiveCondition.PAIR_COMPARATOR.compare(o1It.next(), o2It.next());
                    }
                    return comp;
                }
            }
        };

    /**
     * This is the unique Condition TRUE.
     */
    /*
     * The implementation has to ensure that whenever the logical
     * result TRUE is returned then really this Condition is returned
     */
    public static final QActiveCondition TRUE;

    static {
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> orCondition =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        orCondition.add(new TreeSet<Pair<FunctionSymbol, Integer>>(QActiveCondition.PAIR_COMPARATOR));
        TRUE = new QActiveCondition(orCondition);
    }

    /**
     * checks whether this condition is true or false
     * @return
     */
    public boolean isBoolean() {
        return this == QActiveCondition.TRUE || !this.isSatisfiable();
    }

    /**
     * checks whether the given condition is satisfiable;
     * @return
     */
    public boolean isSatisfiable() {
        return !this.orCondition.isEmpty();
    }

    /**
     * determines whether rule and or reversed rule are usable,
     * requires that afs is fully specified for all f/i in this
     * QActiveCondition.
     * @param afs
     * @return
     */
    public Direction determineOrientation(final ExtendedAfs afs) {
        boolean normal = false;
        boolean reverse = false;

        outerLoop: for (final Set<Pair<FunctionSymbol, Integer>> andCondition : this.orCondition) {
            Direction dir = null;
            for (final Pair<FunctionSymbol, Integer> fi : andCondition) {
                switch (afs.filterPosition(fi.x, fi.y)) {
                case None:
                    continue outerLoop;
                case Wild:
                    if (dir == null) {
                        dir = Direction.Both;
                    } else {
                        throw new RuntimeException("Only one non-incr condition allowed!");
                    }
                    break;
                case Incr:
                    break;
                case Decr:
                    if (dir == null) {
                        dir = Direction.Reversed;
                    } else {
                        throw new RuntimeException("Only one non-incr condition allowed!");
                    }
                    break;
                default:
                    throw new RuntimeException("don't deliver null, please!");
                }
            }
            if (dir == null) {
                normal = true;
            } else if (dir == Direction.Reversed) {
                reverse = true;
            } else { // dir = Both
                normal = true;
                reverse = true;
            }

            // if the rule is always oriented in both direction,
            // then we don't have to look at the other possibilities
            if (normal && reverse) {
                break;
            }
        }

        return normal ? (reverse ? Direction.Both : Direction.Normal) : (reverse ? Direction.Reversed : Direction.None);
    }

    /**
     * returns a specialized QActiveCondition w.r.t. the AFS
     *
     * @param afs
     * @return this, if there was no change, and otherwise a new QActiveCondition corresponding to the specialization
     *  w.r.t. the given afs.
     */
    public QActiveCondition specialize(final Afs afs) {
        if (this == QActiveCondition.TRUE) {
            return this;
        } else {
            boolean changed = false;
            final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> oldOrConditions =
                new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
            final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> simplifiedOrConditions =
                new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);

            loop_And_Conditions: for (final SortedSet<Pair<FunctionSymbol, Integer>> andCondition : this.orCondition) {
                final SortedSet<Pair<FunctionSymbol, Integer>> newAndCondition = QActiveCondition.specializeAndCondition(afs, andCondition);
                if (newAndCondition == andCondition) {
                    final int n = andCondition.size();
                    // check whether we have a simpler version already
                    for (final SortedSet<Pair<FunctionSymbol, Integer>> simplified : simplifiedOrConditions) {
                        // note that these two sets cannot be equal by construction
                        if (simplified.size() < n && QActiveCondition.isSuperSetOf(newAndCondition, simplified) == 1) {
                            continue loop_And_Conditions;
                        }
                    }

                    // no simplified version available, so keep the old condition as it is
                    oldOrConditions.add(andCondition);
                } else if (newAndCondition == null) {
                    // the condition becomes unsatisfiable by the afs
                    // do not add something
                    changed = true;
                } else {
                    // we have a new simplified condition
                    // perhaps throw out some older simplified conditions

                    changed = true;

                    boolean reallyNew = false;
                    final int newSize = newAndCondition.size();
                    final Iterator<SortedSet<Pair<FunctionSymbol, Integer>>> simplIt = simplifiedOrConditions.iterator();
                    while (simplIt.hasNext()) {
                        final SortedSet<Pair<FunctionSymbol, Integer>> oldSimplified = simplIt.next();
                        final int oldSize = oldSimplified.size();

                        if (oldSize <= newSize) {
                            if (!reallyNew) {
                                // if the new condition is really new then it cannot be a superset of any old simpl. condition
                                if (QActiveCondition.isSuperSetOf(newAndCondition, oldSimplified) >= 0) {
                                    // we already have this new condition or a simpler version
                                    continue loop_And_Conditions;
                                }
                            }
                        } else {
                            if (QActiveCondition.isSuperSetOf(oldSimplified, newAndCondition) == 1) {
                                // the newAndCondition is simpler
                                simplIt.remove();
                                reallyNew = true;
                            }
                        }
                    }

                    // we should add the newAndCondition to the simplification condition
                    simplifiedOrConditions.add(newAndCondition);

                    // finally throw out some oldConditions which may be simplified due to this
                    // new simplified and condition
                    final Iterator<SortedSet<Pair<FunctionSymbol, Integer>>> oldIt = oldOrConditions.iterator();
                    while (oldIt.hasNext()) {
                        final SortedSet<Pair<FunctionSymbol, Integer>> oldAndCondition = oldIt.next();
                        if (oldAndCondition.size() > newSize && QActiveCondition.isSuperSetOf(oldAndCondition, newAndCondition) >= 0) {
                            oldIt.remove();
                        }
                    }

                }
            }
            if (changed) {
                SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> resultSet;
                if (oldOrConditions.size() > simplifiedOrConditions.size()) {
                    oldOrConditions.addAll(simplifiedOrConditions);
                    resultSet = oldOrConditions;
                } else {
                    simplifiedOrConditions.addAll(oldOrConditions);
                    resultSet = simplifiedOrConditions;
                }
                if (resultSet.size() == 1 && resultSet.iterator().next().isEmpty()) {
                    return QActiveCondition.TRUE;
                } else {
                    return new QActiveCondition(resultSet);
                }
            } else {
                return this;
            }

        }
    }

    /**
     * specializes the andCondition according to the given AFS
     * @param afs
     * @param andCondition
     * @return the identical andCondition, if nothing was changed,
     * and a specialized Condition otherwise; null indicates an unsatisfiable condition
     */
    private static SortedSet<Pair<FunctionSymbol, Integer>> specializeAndCondition(final Afs afs,
        SortedSet<Pair<FunctionSymbol, Integer>> andCondition) {
        boolean changed = false;
        Iterator<Pair<FunctionSymbol, Integer>> it = andCondition.iterator();
        while (it.hasNext()) {
            final Pair<FunctionSymbol, Integer> fPos = it.next();
            final YNM status = afs.filterPosition(fPos.x, fPos.y);
            if (status == YNM.NO) {
                return null;
            } else if (status == YNM.YES) {
                if (!changed) {
                    // only create a new set on demand
                    changed = true;
                    andCondition = new TreeSet<>(andCondition);
                    it = andCondition.tailSet(fPos).iterator();
                    it.next();
                }
                it.remove();
            }
        }
        return andCondition;
    }

    /**
     * this method merges to simplified conditions (seen as set(conjunction) of set(disjunction) of Pairs(fs, pos).
     * both conditions have to be in simplified form, i.e. dropping any element of any of the sets will
     * cause change the logical meaning. Eg. x or (x and y) is not simplified, as one can express this as
     * x alone.
     * In the implementation this is checked by the fact that every two sets representing conjunctions are
     * not subset of each other.
     * @param left
     * @param right
     * @return
     */
    private static SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> union(final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> left,
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> right) {
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> uniqueLeft =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> uniqueRight =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);
        final SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> both =
            new TreeSet<SortedSet<Pair<FunctionSymbol, Integer>>>(QActiveCondition.AND_COMPARATOR);

        final Iterator<SortedSet<Pair<FunctionSymbol, Integer>>> itLeft = left.iterator();
        final Iterator<SortedSet<Pair<FunctionSymbol, Integer>>> itRight = right.iterator();
        SortedSet<Pair<FunctionSymbol, Integer>> candLeft = null;
        SortedSet<Pair<FunctionSymbol, Integer>> candRight = null;
        SortedSet<Pair<FunctionSymbol, Integer>> cand = null;

        while (true) {
            if (candLeft == null) {
                candLeft = itLeft.hasNext() ? itLeft.next() : null;
            }
            if (candRight == null) {
                candRight = itRight.hasNext() ? itRight.next() : null;
            }
            int dir;
            if (candLeft == null) {
                if (candRight == null) {
                    break;
                } else {
                    dir = 1;
                }
            } else {
                if (candRight == null) {
                    dir = -1;
                } else {
                    dir = QActiveCondition.AND_COMPARATOR.compare(candLeft, candRight);
                }
            }

            if (dir == 0) {
                // equal and-conditions, don't have to checked!
                both.add(candLeft);
                candLeft = null;
                candRight = null;
            } else {
                // get the smaller candidat
                // and the opposite testSet
                SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> non_opposite;
                SortedSet<SortedSet<Pair<FunctionSymbol, Integer>>> opposite;
                if (dir < 0) {
                    cand = candLeft;
                    candLeft = null;
                    non_opposite = uniqueLeft;
                    opposite = uniqueRight;
                } else {
                    cand = candRight;
                    candRight = null;
                    non_opposite = uniqueRight;
                    opposite = uniqueLeft;
                }

                // now check whether we have to insert this candidate
                final int candSize = cand.size();
                int outcome = 2;
                for (final SortedSet<Pair<FunctionSymbol, Integer>> oppSet : opposite) {
                    final int oppSize = oppSet.size();
                    if (oppSize < candSize) {
                        if (QActiveCondition.isSuperSetOf(cand, oppSet) >= 0) {
                            // we do not have to insert this set
                            // as a subset was on the other side
                            outcome = 0;
                            break;
                        }
                    } else if (oppSize == candSize) {
                        // okay, we have to insert this set
                        // but possibly we already have seen this set already before
                        // and stored it later in the oppSet
                        outcome = 1;
                        break;
                    } else {
                        // we definitely have to insert this set
                        break;
                    }
                }

                if (outcome == 1) {
                    final boolean hadIt = opposite.remove(cand);
                    if (hadIt) {
                        both.add(cand);
                    } else {
                        non_opposite.add(cand);
                    }
                } else if (outcome == 2) {
                    non_opposite.add(cand);
                }

            }

        }

        uniqueLeft.addAll(uniqueRight);
        uniqueLeft.addAll(both);
        return uniqueLeft;
    }

    /**
     * returns this or formula
     * @param formula
     * @return
     */
    public QActiveCondition or(final QActiveCondition formula) {
        if (this == QActiveCondition.TRUE || formula == QActiveCondition.TRUE) {
            return QActiveCondition.TRUE;
        } else {
            return new QActiveCondition(QActiveCondition.union(this.orCondition, formula.orCondition));
        }
    }

    @Override
    public boolean equals(final Object other) {
        final QActiveCondition cond = (QActiveCondition) other;
        if (this.hashValid && cond.hashValid) {
            if (this.hashCode() != cond.hashCode()) {
                return false;
            }
        }

        return QActiveCondition.equalSets(this.orCondition, cond.orCondition);
    }

    /**
     * compares whether the two sets are equal
     * @param as
     * @param bs
     */
    private static final <T> boolean equalSets(final SortedSet<T> as, final SortedSet<T> bs) {
        if (as.size() != bs.size()) {
            return false;
        }
        final Comparator<? super T> comp = as.comparator();
        final Iterator<T> asIt = as.iterator();
        final Iterator<T> bsIt = bs.iterator();
        while (asIt.hasNext()) {
            final T a = asIt.next();
            final T b = bsIt.next();
            if (comp.compare(a, b) != 0) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        if (!this.hashValid) {
            this.hash = this.orCondition.hashCode();
        }
        return this.hash;
    }

    /**
     * returns the internal set-representation of this
     * condition. See class description for more details
     * on this representation.
     * Do not modify this set!!!
     * @return
     */
    public Set<? extends Set<Pair<FunctionSymbol, Integer>>> getSetRepresentation() {
        return this.orCondition;
    }

}
