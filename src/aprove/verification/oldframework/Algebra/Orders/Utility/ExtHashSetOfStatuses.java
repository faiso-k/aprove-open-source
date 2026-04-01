package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.strategies.Abortions.*;

/** Implementation of an extended hash set of statuses.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class ExtHashSetOfStatuses<T> extends HashSet<Status<T>> {
    private List<T> set;

    /* constructors */

    private ExtHashSetOfStatuses(List<T> set) {
        super();
        this.set = new ArrayList<T>(set);
    }

    /** Creates a new instance of <code>ExtVectorOfStatuses</code>.
     * @param set   The statuses that'll be elements will be statuses on this set
     */
    public static <U> ExtHashSetOfStatuses<U> create(List<U> set) {
        return new ExtHashSetOfStatuses<U>(set);
    }

    /** Creates a new instance of <code>ExtVectorOfStatuses</code>.
     */
    public static <U> ExtHashSetOfStatuses<U> create() {
        return new ExtHashSetOfStatuses<U>(new ArrayList<U>());
    }

    public ExtHashSetOfStatuses<T> deepcopy() {
        ExtHashSetOfStatuses<T> res = ExtHashSetOfStatuses.create(this.set);
        Iterator<Status<T>> i = this.iterator();
        Status<T> s;

        while(i.hasNext()) {
            s = i.next();
            res.add(s.deepcopy());
        }

        return res;
    }


    /** Returns an <code>ExtHashSetOfStatuses</code> which contains the minimal
     * statuses from this set.
     * A status <code>P</code> in this set is minimal iff
     * there's no status <code>Q</code> in this set s.t.
     * <code>Q.isContainedIn(P) == true</code>
     * and <code>P != Q </code>.
     * @see   Status#isContainedIn(Status)
     */
    public ExtHashSetOfStatuses<T> minimalElements() throws StatusException {
        ExtHashSetOfStatuses<T> res;
        Iterator<Status<T>> i1;
        Iterator<Status<T>> i2;
        Status<T> P;
        Status<T> Q;
        boolean foundSmaller;

        res = ExtHashSetOfStatuses.create(this.set);

        i1 = this.iterator();
        while(i1.hasNext()) {
            P = i1.next();
            i2 = this.iterator();
            foundSmaller = false;
            while(i2.hasNext() && !foundSmaller) {
                Q = i2.next();
                if(!P.equals(Q)) {
                    foundSmaller = Q.isContainedIn(P);
                }
            }
            if(!foundSmaller) {
                res.add(P);
            }
        }

        return res;
    }

    /** Returns a <code>Status</code> that is the intersection of all posets
     * contained in this object, returns an empty status if this object
     * contains no statuses.
     * @see   Status#intersect(Status)
     */
    public Status<T> intersectAll() throws StatusException {
        Status<T> res = Status.create(Poset.create(this.set),
                StatusMap.create(this.set));

        if(!this.isEmpty()) {
            Iterator<Status<T>> i = this.iterator();

            res = i.next();
            while(i.hasNext()) {
                res = res.intersect(i.next());
            }
        }

        return res;
    }

    /** Returns a <code>ExtHashSetOfStatuses</code> that contains all statuses
     * that can be constructed by merging one status of this object with
     * one status of <code>other</code>.
     * @see   Status#mergeSlow(Status)
     */
    public ExtHashSetOfStatuses<T> mergeAllSlow(Abortion aborter, ExtHashSetOfStatuses<T> other) throws AbortionException {
        ExtHashSetOfStatuses<T> res = ExtHashSetOfStatuses.create(this.set);
        Iterator<Status<T>> i1 = this.iterator();
        Iterator<Status<T>> i2;
        Status<T> P;
        Status<T> Q;
        Status<T> PuQ;

        if(other!=null) {
            while(i1.hasNext()) {
                P = i1.next();
                i2 = other.iterator();
                while(i2.hasNext()) {
                    aborter.checkAbortion();
                    Q = i2.next();
                    try {
                        PuQ = P.mergeSlow(Q);
                        res.add(PuQ);
                    }
                    catch(Exception e) {
                        /* don't add it, probably incompatible */
                    }
                }
            }
        }

        return res;
    }

    /** Returns a <code>ExtHashSetOfStatuses</code> that contains all statuses
     * that can be constructed by merging one status of this object with
     * one status of <code>other</code>.
     * @see   Status#merge(Status)
     */
    public ExtHashSetOfStatuses<T> mergeAll(ExtHashSetOfStatuses<T> other) {
        ExtHashSetOfStatuses<T> res = ExtHashSetOfStatuses.create(this.set);
        Iterator<Status<T>> i1 = this.iterator();
        Iterator<Status<T>> i2;
        Status<T> P;
        Status<T> Q;
        Status<T> PuQ;

        if(other!=null) {
            while(i1.hasNext()) {
                P = i1.next();
                i2 = other.iterator();
                while(i2.hasNext()) {
                    Q = i2.next();
                    try {
                        PuQ = P.merge(Q);
                        res.add(PuQ);
                    }
                    catch(Exception e) {
                        /* don't add it, probably incompatible */
                    }
                }
            }
        }

        return res;
    }

    /** Returns a new <code>ExtHashSetOfStatuses</code> containing the elements
     * of this object and the elements of <code>other</code>.
     */
    public ExtHashSetOfStatuses<T> union(ExtHashSetOfStatuses<T> other) {
        ExtHashSetOfStatuses<T> res = (ExtHashSetOfStatuses)this.clone();
        Iterator<Status<T>> i;

        if(other!=null) {
            i = other.iterator();
            while(i.hasNext()) {
                res.add(i.next());
            }
        }

        return res;
    }

    /** Returns a new <code>ExtHashSetOfStatuses/code> containing the elements
     * of this object and the elements of <code>other</code>.
     */
    public ExtHashSetOfStatuses<T> project(Collection<T> sig) {
        ExtHashSetOfStatuses<T> res = ExtHashSetOfStatuses.create();
        for (Status<T> P : this) {
            res.add(P.project(sig));
        }
        return res;
    }
}
