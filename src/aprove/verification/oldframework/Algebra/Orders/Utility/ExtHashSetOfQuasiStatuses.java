package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.strategies.Abortions.*;

/** Implementation of an extended hash set of quasi statuses.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class ExtHashSetOfQuasiStatuses<T> extends HashSet<QuasiStatus<T>> {
    private List<T> set;

    /* constructors */

    private ExtHashSetOfQuasiStatuses(List<T> set) {
        super();
        this.set = new ArrayList<T>(set);
    }

    /** Creates a new instance of <code>ExtVectorOfQuasiStatuses</code>.
     * @param set   The quasi statuses that'll be elements will be quasi statuses on this set
     */
    public static <U> ExtHashSetOfQuasiStatuses<U> create(List<U> set) {
        return new ExtHashSetOfQuasiStatuses<U>(set);
    }

    /** Creates a new instance of <code>ExtVectorOfQuasiStatuses</code>.
     */
    public static <U> ExtHashSetOfQuasiStatuses<U> create() {
        return new ExtHashSetOfQuasiStatuses<U>(new ArrayList<U>());
    }

    public ExtHashSetOfQuasiStatuses<T> deepcopy() {
        ExtHashSetOfQuasiStatuses<T> res = ExtHashSetOfQuasiStatuses.create(this.set);
        Iterator<QuasiStatus<T>> i = this.iterator();
        QuasiStatus<T> s;

        while(i.hasNext()) {
            s = i.next();
            res.add(s.deepcopy());
        }

        return res;
    }


    /** Returns an <code>ExtHashSetOfQuasiStatuses</code> which contains the minimal
     * quasi statuses from this set.
     * A quasi status <code>P</code> in this set is minimal iff
     * there's no quasi status <code>Q</code> in this set s.t.
     * <code>Q.isContainedIn(P) == true</code>
     * and <code>P != Q </code>.
     * @see   QuasiStatus#isContainedIn(QuasiStatus)
     */
    public ExtHashSetOfQuasiStatuses<T> minimalElements() throws QuasiStatusException {
        ExtHashSetOfQuasiStatuses<T> res;
        Iterator<QuasiStatus<T>> i1;
        Iterator<QuasiStatus<T>> i2;
        QuasiStatus<T> P;
        QuasiStatus<T> Q;
        boolean foundSmaller;

        res = ExtHashSetOfQuasiStatuses.create(this.set);

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

    /** Returns a <code>QuasiStatus</code> that is the intersection of all posets
     * contained in this object, returns an empty quasi status if this object
     * contains no quasi statuses.
     * @see   QuasiStatus#intersect(QuasiStatus)
     */
    public QuasiStatus<T> intersectAll() throws QuasiStatusException {
        QuasiStatus<T> res = QuasiStatus.create(Qoset.create(this.set),
                StatusMap.create(this.set));

        if(!this.isEmpty()) {
            Iterator<QuasiStatus<T>> i = this.iterator();

            res = i.next();
            while(i.hasNext()) {
                res = res.intersect(i.next());
            }
        }

        return res;
    }

    /** Returns a <code>ExtHashSetOfQuasiStatuses</code> that contains all
     * quasi statuses
     * that can be constructed by merging one quasi status of this object with
     * one quasi status of <code>other</code>.
     * @see   QuasiStatus#mergeSlow(QuasiStatus)
     */
    public ExtHashSetOfQuasiStatuses<T> mergeAllSlow(Abortion aborter, ExtHashSetOfQuasiStatuses<T> other) throws AbortionException {
        ExtHashSetOfQuasiStatuses<T> res = ExtHashSetOfQuasiStatuses.create(this.set);
        Iterator<QuasiStatus<T>> i1 = this.iterator();
        Iterator<QuasiStatus<T>> i2;
        QuasiStatus<T> P;
        QuasiStatus<T> Q;
        QuasiStatus<T> PuQ;

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

    /** Returns a <code>ExtHashSetOfQuasiStatuses</code> that contains all
     * quasi statuses
     * that can be constructed by merging one quasi status of this object with
     * one quasi status of <code>other</code>.
     * @see   QuasiStatus#merge(QuasiStatus)
     */
    public ExtHashSetOfQuasiStatuses<T> mergeAll(ExtHashSetOfQuasiStatuses<T> other) {
        ExtHashSetOfQuasiStatuses<T> res = ExtHashSetOfQuasiStatuses.create(this.set);
        Iterator<QuasiStatus<T>> i1 = this.iterator();
        Iterator<QuasiStatus<T>> i2;
        QuasiStatus<T> P;
        QuasiStatus<T> Q;
        QuasiStatus<T> PuQ;

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

    /** Returns a new <code>ExtHashSetOfQuasiStatuses</code> containing the elements
     * of this object and the elements of <code>other</code>.
     */
    public ExtHashSetOfQuasiStatuses<T> union(ExtHashSetOfQuasiStatuses<T> other) {
        ExtHashSetOfQuasiStatuses<T> res = (ExtHashSetOfQuasiStatuses)this.clone();
        Iterator<QuasiStatus<T>> i;

        if(other!=null) {
            i = other.iterator();
            while(i.hasNext()) {
                res.add(i.next());
            }
        }

        return res;
    }

    /** Returns a new <code>ExtHashSetOfQuasiStatuses/code> containing the elements
     * of this object and the elements of <code>other</code>.
     */
    public ExtHashSetOfQuasiStatuses<T> project(Collection<T> sig) {
        ExtHashSetOfQuasiStatuses<T> res = ExtHashSetOfQuasiStatuses.create();
        for (QuasiStatus<T> Q : this) {
            res.add(Q.project(sig));
        }
        return res;
    }
}