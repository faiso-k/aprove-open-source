package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * The monotonicity constraints { f/3, g/2, h/0 } mean that f must be
 * monotonic(ally increasing) in its 3rd arg, g in its 2nd arg and h in its 0th
 * (remember that internally, arg indices are counted from 0 upwards).
 *
 * Intended usage: If the monotonicity constraint is fulfilled by an order, we
 * can be sure that strict decrease of a corresponding rule l -> r also implies
 * overall decrease. (Cf. the class QActiveCondition, which looks similar, but
 * has a slightly different meaning.)
 *
 * Note that there is also another notion of "monotonicity constraints" in the
 * termination literature and indeed now also in AProVE. Apart from the name,
 * these notions do not have much in common, though, and the name clash is a
 * mere coincidence.
 *
 * @author fuhs
 * @author micpar
 * @version $Id$
 */
public class MonotonicityConstraints implements Immutable {

    private ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> constraints;

    public static final MonotonicityConstraints TRUE = new MonotonicityConstraints(
            ImmutableCreator.create(
                    java.util.Collections.<FunctionSymbol, ImmutableSet<Integer>>emptyMap()));

    private MonotonicityConstraints(ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> theConstraints) {
        this.constraints = theConstraints;
    }

    /**
     * @param theConstraints - to be encapsulated by this (non-null!)
     * @return
     */
    public static MonotonicityConstraints create(ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> theConstraints) {
        return new MonotonicityConstraints(theConstraints);
    }

    /**
     * @return the constraints
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> getConstraints() {
        return this.constraints;
    }

    public ImmutableSet<Integer> getConstraint(FunctionSymbol f) {
        return this.constraints.get(f);
    }

    /**
     * @param other
     * @return a MonotonicityConstraint that is satisfied by the same orders
     *  as the conjunction of <code>this</code> and <code>other</code>
     */
    public MonotonicityConstraints uniteWith(MonotonicityConstraints other) {
        if (MonotonicityConstraints.TRUE.equals(this)) {
            return other;
        }
        if (MonotonicityConstraints.TRUE.equals(other)) {
            return this;
        }
        Map<FunctionSymbol, ImmutableSet<Integer>> res =
            new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        for (Entry<FunctionSymbol, ImmutableSet<Integer>> fMon : this.constraints.entrySet()) {
            FunctionSymbol f = fMon.getKey();
            ImmutableSet<Integer> thisMon = fMon.getValue();
            ImmutableSet<Integer> otherMon = other.getConstraint(f);
            ImmutableSet<Integer> newMon;
            if (otherMon == null) {
                newMon = thisMon;
            }
            else {
                Set<Integer> protoNewMon = new LinkedHashSet<Integer>();
                protoNewMon.addAll(thisMon);
                protoNewMon.addAll(otherMon);
                newMon = ImmutableCreator.create(protoNewMon);
            }
            res.put(f, newMon);
        }
        for (Entry<FunctionSymbol, ImmutableSet<Integer>> fMon : other.constraints.entrySet()) {
            FunctionSymbol f = fMon.getKey();
            // handle symbols only beknownst to other
            if (! this.constraints.containsKey(f)) {
                ImmutableSet<Integer> otherMon = fMon.getValue();
                res.put(f, otherMon);
            }
        }
        MonotonicityConstraints result = MonotonicityConstraints.create(
                ImmutableCreator.create(res));
        return result;
    }

    /**
     * @param order - non-null, must know all function symbols
     *  that occur in this
     * @return whether this MonotonicityConstraints is satisfied by order
     */
    public boolean isSatisfiedBy(PartiallyMonotonicOrder order) {
        for (Entry<FunctionSymbol, ImmutableSet<Integer>> fReqs : this.constraints.entrySet()) {
            FunctionSymbol f = fReqs.getKey();
            for (Integer i : fReqs.getValue()) {
                if (! order.fIsMonotonicInArg(f, i)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * @return how many atomic conjuncts this consists of
     */
    public int size() {
        return this.constraints.size();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int PRIME = 31;
        int result = PRIME + ((this.constraints == null) ? 0 : this.constraints.hashCode());
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
        final MonotonicityConstraints other = (MonotonicityConstraints) obj;
        if (this.constraints == null) {
            if (other.constraints != null) {
                return false;
            }
        }
        else if (!this.constraints.equals(other.constraints)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        // TODO make output human-readable, e.g., count arguments
        // from 1 upwards, not from 0 upwards for export
        return this.constraints.toString();
    }
}
