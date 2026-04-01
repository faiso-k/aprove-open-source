package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.strategies.Abortions.*;

/** Implementation of an extended hash set of qosets.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class ExtHashSetOfQosets<T> extends HashSet<Qoset<T>> {
    private List<T> set;

    /* constructors */

    private ExtHashSetOfQosets(List<T> set) {
        super();
        this.set = new ArrayList<T>(set);
    }

    private ExtHashSetOfQosets(ExtHashSetOfQosets<T> old) {
        super(old);
        this.set = new ArrayList<T>(old.set);
    }

    /** Creates a new instance of <code>ExtVectorOfQosets</code>.
     * @param set   The qosets that'll be elements will be qosets on this set
     */
    public static <U> ExtHashSetOfQosets<U> create(List<U> set) {
        return new ExtHashSetOfQosets<U>(set);
    }

    /** Creates a new instance of <code>ExtVectorOfQosets</code>.
     */
    public static <U> ExtHashSetOfQosets<U> create() {
        return new ExtHashSetOfQosets<U>(new ArrayList<U>());
    }

    public ExtHashSetOfQosets<T> deepcopy() {
        ExtHashSetOfQosets<T> res = ExtHashSetOfQosets.create(this.set);
        Iterator<Qoset<T>> i = this.iterator();
        Qoset<T> s;

        while(i.hasNext()) {
            s = i.next();
            res.add(s.deepcopy());
        }

        return res;
    }


    /** Returns an <code>ExtHashSetOfQosets</code> which contains the minimal
     * qosets from this set.
     * A qoset <code>P</code> in this set is minimal iff
     * there's no qoset <code>Q</code> in this set s.t.
     * <code>Q.isContainedIn(P) == true</code>
     * and <code>P != Q </code>.
     * @see   Qoset#isContainedIn(Qoset)
     */
    public ExtHashSetOfQosets<T> minimalElements() throws QosetException {
        ExtHashSetOfQosets<T> res;
        Iterator<Qoset<T>> i1;
        Iterator<Qoset<T>> i2;
        Qoset<T> P;
        Qoset<T> Q;
        boolean foundSmaller;

        res = ExtHashSetOfQosets.create(this.set);

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
                /* there's no Q that's smaller than P */
                res.add(P);
            }
        }
        return res;
    }

    /** Returns a <code>Qoset</code> that is the intersection of all qosets
     * contained in this object, returns an empty qoset if this object
     * contains no qosets.
     * @see   Qoset#intersect(Qoset)
     */
    public Qoset<T> intersectAll() throws QosetException {
        Qoset<T> res = Qoset.create(this.set);

        if(!this.isEmpty()) {
            Iterator<Qoset<T>> i = this.iterator();

            res = i.next();
            while(i.hasNext()) {
                res = res.intersect(i.next());
            }
        }

        return res;
    }

    /** Returns a <code>ExtHashSetOfQosets</code> that contains all qosets
     * that can be constructed by merging one qoset of this object with
     * one qoset of <code>other</code>.
     * @see   Qoset#mergeSlow(Qoset)
     */
    public ExtHashSetOfQosets<T> mergeAllSlow(Abortion aborter, ExtHashSetOfQosets<T> other) throws AbortionException {
        ExtHashSetOfQosets<T> res = ExtHashSetOfQosets.create(this.set);
        Iterator<Qoset<T>> i1 = this.iterator();
        Iterator<Qoset<T>> i2;
        Qoset<T> P;
        Qoset<T> Q;
        Qoset<T> PuQ;

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
                    catch(QosetException e) {
                        /* don't add it, probably not irreflexive */
                    }
                }
            }
        }

        return res;
    }

    /** Returns a <code>ExtHashSetOfQosets</code> that contains all qosets
     * that can be constructed by merging one qoset of this object with
     * one qoset of <code>other</code>.
     * @see   Qoset#merge(Qoset)
     */
    public ExtHashSetOfQosets<T> mergeAll(ExtHashSetOfQosets<T> other) {
        ExtHashSetOfQosets<T> res = ExtHashSetOfQosets.create(this.set);
        Iterator<Qoset<T>> i1 = this.iterator();
        Iterator<Qoset<T>> i2;
        Qoset<T> P;
        Qoset<T> Q;
        Qoset<T> PuQ;

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
                    catch(QosetException e) {
                        /* don't add it, probably not irreflexive */
                    }
                }
            }
        }

        return res;
    }

    /** Returns a new <code>ExtHashSetOfQosets</code> containing the elements
     * of this object and the elements of <code>other</code>.
     */
    public ExtHashSetOfQosets<T> union(ExtHashSetOfQosets<T> other) {
        ExtHashSetOfQosets<T> res = new ExtHashSetOfQosets<T>(this);
        Iterator<Qoset<T>> i;

        if(other!=null) {
            i = other.iterator();
            while(i.hasNext()) {
                res.add(i.next());
            }
        }

        return res;
    }

}
