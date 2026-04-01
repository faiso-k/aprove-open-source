package aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
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
 * { {f/0, f/3}, {g/1, f/2}, {g/2} } represents the formular
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
 */
public class IActiveCondition implements Immutable {

    public static enum IDirection {
        Normal, Reversed, Both, None
    };

    public static enum IDependence {
        None, Incr, Decr, Wild
    };

    public interface IExtendedAfs {
        IDependence filterPosition(FunctionSymbol f, int i);
    }

    public static List<ImmutablePair<FunctionSymbol, Integer>> pathToRoot(TRSTerm t, final Position p) {
        if (p.getDepth() > 0) {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final List<ImmutablePair<FunctionSymbol, Integer>> res =
                new ArrayList<ImmutablePair<FunctionSymbol, Integer>>(p.getDepth());
            final Iterator<Integer> iter = p.iterator();
            while (iter.hasNext()) {
                final Integer i = iter.next();
                res.add(new ImmutablePair<FunctionSymbol, Integer>(fa.getRootSymbol(), i));
                if (iter.hasNext()) {
                    t = ((TRSFunctionApplication) t).getArgument(i);
                }
            }
            return res;
        } else {
            return Collections.<ImmutablePair<FunctionSymbol, Integer>>emptyList();
        }
    }

    // the set of set of (f/i) means
    // whenever orCondition contains one set andConds where
    // all (f/i) are present in the filtering,
    // then the Condition is satisfied
    private final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> orCondition;

    private static boolean firstBuild = true;

    public static IActiveCondition create(final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> orCondition) {
        return new IActiveCondition(orCondition);
    }

    private IActiveCondition(
            final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> orCondition) {
        this.orCondition = orCondition;
        if (Globals.useAssertions) {
            if (IActiveCondition.firstBuild) { // the first build is TRUE
                IActiveCondition.firstBuild = false;
            } else {
                // later there must not be build an equivalent IActiveCondition to TRUE.
                assert (orCondition.size() != 1 || !orCondition.iterator().next().isEmpty());
            }
        }
    }

    @Override
    public String toString() {
        boolean firstOr = true;
        String res = "";
        for (final Set<ImmutablePair<FunctionSymbol, Integer>> andSet : this.orCondition) {
            boolean firstAnd = true;
            String sub = "";
            for (final ImmutablePair<FunctionSymbol, Integer> cond : andSet) {
                if (firstAnd) {
                    firstAnd = false;
                    sub += "{";
                } else {
                    sub += ", ";
                }
                sub += cond.x.getName() + "/" + (cond.y);
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
    public IActiveCondition and(final IActiveCondition formula) {
        if (this.equals(IActiveCondition.TRUE)) {
            return formula;
        } else if (formula.equals(IActiveCondition.TRUE)) {
            return this;
        } else {
            ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> oneOr = this.orCondition;
            ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> otherOr = formula.orCondition;
            if (oneOr.size() > otherOr.size()) {
                oneOr = otherOr;
                otherOr = this.orCondition;
            }
            ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> res;
            if (oneOr.size() == 0) {
                res =
                    ImmutableCreator.create(Collections.<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>>emptySet());
            } else {
                final Iterator<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> it = oneOr.iterator();
                ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> conjunction = it.next();
                res = IActiveCondition.and(otherOr, conjunction);

                while (it.hasNext()) {
                    conjunction = it.next();
                    res = IActiveCondition.union(res, IActiveCondition.and(otherOr, conjunction));
                }
            }
            return new IActiveCondition(res);
        }
    }

    /**
     * computes "formula and conjunction"
     * @param formula
     * @param conjunction
     */
    private static ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> and(final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> formula,
        final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> conjunction) {
        if (conjunction.isEmpty()) {
            return formula;
        }
        if (conjunction.size() == 1) {
            return IActiveCondition.and(formula, conjunction.iterator().next());
        }

        final Set<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> newOrCondition =
            new LinkedHashSet<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>>();
        for (final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> andCond : formula) {
            final Set<ImmutablePair<FunctionSymbol, Integer>> newAndCond =
                new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>(andCond);
            newAndCond.addAll(conjunction);
            newOrCondition.add(ImmutableCreator.create(newAndCond));
        }
        return ImmutableCreator.create(newOrCondition);
    }

    /**
     * computes "this and f/position"
     * @param f
     * @param position
     */
    public IActiveCondition and(final FunctionSymbol f, final int position) {
        final ImmutablePair<FunctionSymbol, Integer> newCond = new ImmutablePair<FunctionSymbol, Integer>(f, position);
        return new IActiveCondition(IActiveCondition.and(this.orCondition, newCond));
    }

    /**
     * computes "formula and newCond"
     * @param formula
     * @param newCond the condition f/i to be added
     */
    private static ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> and(final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> formula,
        final ImmutablePair<FunctionSymbol, Integer> newCond) {
        final Set<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> newOrCondition =
            new LinkedHashSet<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>>();
        for (final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> andCond : formula) {
            if (andCond.contains(newCond)) {
                newOrCondition.add(andCond);
            } else {
                final Set<ImmutablePair<FunctionSymbol, Integer>> newAndCond =
                    new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>(andCond);
                newAndCond.add(newCond);
                newOrCondition.add(ImmutableCreator.create(newAndCond));
            }
        }
        return ImmutableCreator.create(newOrCondition);
    }

    /**
     * This is the unique Condition TRUE.
     */
    /*
     * The implementation has to ensure that whenever the logical
     * result TRUE is returned then really this Condition is returned
     */
    public static final IActiveCondition TRUE;

    static {
        final Set<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> orCondition =
            Collections.<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>>singleton(ImmutableCreator.create(Collections.<ImmutablePair<FunctionSymbol, Integer>>emptySet()));
        TRUE = new IActiveCondition(ImmutableCreator.create(orCondition));
    }

    /**
     * checks whether this condition is true or false
     * @return
     */
    public boolean isBoolean() {
        return this.equals(IActiveCondition.TRUE) || !this.isSatisfiable();
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
     * IActiveCondition.
     * @param afs
     * @return
     */
    public IDirection determineOrientation(final IExtendedAfs afs) {
        boolean normal = false;
        boolean reverse = false;

        outerLoop: for (final Set<ImmutablePair<FunctionSymbol, Integer>> andCondition : this.orCondition) {
            IDirection dir = null;
            for (final ImmutablePair<FunctionSymbol, Integer> fi : andCondition) {
                switch (afs.filterPosition(fi.x, fi.y)) {
                case None:
                    dir = IDirection.None;
                    continue outerLoop;
                case Wild:
                    dir = IDirection.Both;
                    break;
                case Incr:
                    if (dir == null) {
                        dir = IDirection.Normal;
                    }
                    break;
                case Decr:
                    if (dir == null || dir == IDirection.Normal) {
                        dir = IDirection.Reversed;
                    } else if (dir == IDirection.Reversed) {
                        dir = IDirection.Normal;
                    }
                    break;
                default:
                    throw new RuntimeException("don't deliver null, please!");
                }
            }
            if (dir == null) {
                // true
                normal = true;
                reverse = true;
            } else if (dir == IDirection.Normal) {
                normal = true;
            } else if (dir == IDirection.Reversed) {
                reverse = true;
            } else if (dir == IDirection.Both) {
                normal = true;
                reverse = true;
            }

            // if the rule is always oriented in both direction,
            // then we don't have to look at the other possibilities
            if (normal && reverse) {
                break;
            }
        }

        return normal ? (reverse ? IDirection.Both : IDirection.Normal) : (reverse ? IDirection.Reversed
            : IDirection.None);
    }

    /**
     * returns a specialized IActiveCondition w.r.t. the AFS
     *
     * @param afs
     * @return this, if there was no change, and otherwise a new IActiveCondition corresponding to the specialization
     *  w.r.t. the given afs.
     */
    public IActiveCondition specialize(final IExtendedAfs afs) {
        if (this.equals(IActiveCondition.TRUE)) {
            return IActiveCondition.TRUE;
        } else {
            boolean changed = false;
            final Set<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> newOrConditions = new LinkedHashSet<>();

            for (final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> andCondition : this.orCondition) {
                final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> newAndCondition =
                    IActiveCondition.specializeAndCondition(afs, andCondition);
                if (newAndCondition != null) {
                    newOrConditions.add(newAndCondition);
                    changed = changed || andCondition != newAndCondition;
                } else {
                    changed = true;
                }
            }
            if (changed) {
                final IActiveCondition iActive = new IActiveCondition(ImmutableCreator.create(newOrConditions));
                if (IActiveCondition.TRUE.equals(iActive)) {
                    return IActiveCondition.TRUE;
                } else {
                    return iActive;
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
    private static ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> specializeAndCondition(final IExtendedAfs afs,
        final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> andCondition) {
        boolean changed = false;
        boolean decr = false;
        ImmutablePair<FunctionSymbol, Integer> lastDecr = null;
        final Iterator<ImmutablePair<FunctionSymbol, Integer>> it = andCondition.iterator();
        final Set<ImmutablePair<FunctionSymbol, Integer>> newAndCondition =
            new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>();
        while (it.hasNext()) {
            final ImmutablePair<FunctionSymbol, Integer> fPos = it.next();
            final IDependence dependence = afs.filterPosition(fPos.x, fPos.y);
            if (dependence == IDependence.None) {
                return null;
            } else if (dependence == IDependence.Wild) {
                return ImmutableCreator.create(Collections.singleton(fPos));
            } else if (dependence == IDependence.Incr) {
                changed = true;
            } else if (dependence == IDependence.Decr) {
                decr = !decr;
                if (lastDecr != null) {
                    changed = true;
                }
                lastDecr = fPos;
            } else {
                newAndCondition.add(fPos);
            }
        }
        if (decr) {
            changed = true;
            newAndCondition.add(lastDecr);
        }
        return changed ? ImmutableCreator.create(newAndCondition) : andCondition;
    }

    /**
     * this method merges two conditions
     * @param left
     * @param right
     * @return
     */
    private static ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> union(final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> left,
        final ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> right) {
        final Set<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> res =
            new LinkedHashSet<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>>(left);
        res.addAll(right);
        return ImmutableCreator.create(res);
    }

    /**
     * returns this or formula
     * @param formula
     * @return
     */
    public IActiveCondition or(final IActiveCondition formula) {
        if (this.equals(IActiveCondition.TRUE) || formula.equals(IActiveCondition.TRUE)) {
            return IActiveCondition.TRUE;
        } else {
            return new IActiveCondition(IActiveCondition.union(this.orCondition, formula.orCondition));
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.orCondition == null) ? 0 : this.orCondition.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
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
        final IActiveCondition other = (IActiveCondition) obj;
        if (this.orCondition == null) {
            if (other.orCondition != null) {
                return false;
            }
        } else if (!this.orCondition.equals(other.orCondition)) {
            return false;
        }
        return true;
    }

    /**
     * returns the internal set-representation of this
     * condition. See class description for more details
     * on this representation.
     * Do not modify this set!!!
     * @return
     */
    public ImmutableSet<? extends ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>> getSetRepresentation() {
        return this.orCondition;
    }

}
