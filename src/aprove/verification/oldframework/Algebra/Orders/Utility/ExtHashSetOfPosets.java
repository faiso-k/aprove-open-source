package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.strategies.Abortions.*;

/** Implementation of an extended hash set of posets.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class ExtHashSetOfPosets<T> extends HashSet<Poset<T>> {
    private List<T> set;

    /* constructors */

    private ExtHashSetOfPosets(List<T> set) {
    super();
    this.set = new ArrayList<T>(set);
    }

    private ExtHashSetOfPosets(ExtHashSetOfPosets<T> old) {
        super(old);
        this.set = new ArrayList<T>(old.set);
    }

    /** Creates a new instance of <code>ExtVectorOfPosets</code>.
     * @param set   The posets that'll be elements will be posets on this set
     */
    public static <U> ExtHashSetOfPosets<U> create(List<U> set) {
    return new ExtHashSetOfPosets<U>(set);
    }

    /** Creates a new instance of <code>ExtVectorOfPosets</code>.
     */
    public static <U> ExtHashSetOfPosets<U> create() {
        return new ExtHashSetOfPosets<U>(new ArrayList<U>());
    }

    public ExtHashSetOfPosets<T> deepcopy() {
    ExtHashSetOfPosets<T> res = ExtHashSetOfPosets.create(this.set);
    Iterator<Poset<T>> i = this.iterator();
    Poset<T> s;

    while(i.hasNext()) {
        s = i.next();
        res.add(s.deepcopy());
    }

    return res;
    }


    /** Returns an <code>ExtHashSetOfPosets</code> which contains the minimal
     * posets from this set.
     * A poset <code>P</code> in this set is minimal iff
     * there's no poset <code>Q</code> in this set s.t.
     * <code>Q.isContainedIn(P) == true</code>
     * and <code>P != Q </code>.
     * @see   Poset#isContainedIn(Poset)
     */
    public ExtHashSetOfPosets<T> minimalElements() throws PosetException {
    ExtHashSetOfPosets<T> res;
        Iterator<Poset<T>> i1;
    Iterator<Poset<T>> i2;
    Poset<T> P;
    Poset<T> Q;
    boolean foundSmaller;

    res = ExtHashSetOfPosets.create(this.set);

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

    /** Returns a <code>Poset</code> that is the intersection of all posets
     * contained in this object, returns an empty poset if this object
     * contains no posets.
     * @see   Poset#intersect(Poset)
     */
    public Poset<T> intersectAll() throws PosetException {
    Poset<T> res = Poset.create(this.set);

    if(!this.isEmpty()) {
        Iterator<Poset<T>> i = this.iterator();

        res = i.next();
        while(i.hasNext()) {
        res = res.intersect(i.next());
        }
    }

    return res;
    }

    /** Returns a <code>ExtHashSetOfPosets</code> that contains all posets
     * that can be constructed by merging one poset of this object with
     * one poset of <code>other</code>.
     * @see   Poset#mergeSlow(Poset)
     */
    public ExtHashSetOfPosets<T> mergeAllSlow(Abortion aborter, ExtHashSetOfPosets<T> other) throws AbortionException {
    ExtHashSetOfPosets<T> res = ExtHashSetOfPosets.create(this.set);
    Iterator<Poset<T>> i1 = this.iterator();
    Iterator<Poset<T>> i2;
    Poset<T> P;
    Poset<T> Q;
    Poset<T> PuQ;

    if(other!=null) {
        while(i1.hasNext()) {
            P = i1.next();
            i2 = other.iterator();
                while(i2.hasNext()) {
                    //aborter.checkAbortion();
            Q = i2.next();
                    try {
                PuQ = P.mergeSlow(Q);
                res.add(PuQ);
            }
            catch(PosetException e) {
                /* don't add it, probably not irreflexive */
            }
            }
        }
    }

    return res;
    }

    /** Returns a <code>ExtHashSetOfPosets</code> that contains all posets
     * that can be constructed by merging one poset of this object with
     * one poset of <code>other</code>.
     * @see   Poset#merge(Poset)
     */
    public ExtHashSetOfPosets<T> mergeAll(ExtHashSetOfPosets<T> other) {
    ExtHashSetOfPosets<T> res = ExtHashSetOfPosets.create(this.set);
    Iterator<Poset<T>> i1 = this.iterator();
    Iterator<Poset<T>> i2;
    Poset<T> P;
    Poset<T> Q;
    Poset<T> PuQ;

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
            catch(PosetException e) {
                /* don't add it, probably not irreflexive */
            }
            }
        }
    }

    return res;
    }

    /** Returns a new <code>ExtHashSetOfPosets</code> containing the elements
     * of this object and the elements of <code>other</code>.
     */
    public ExtHashSetOfPosets<T> union(ExtHashSetOfPosets<T> other) {
    ExtHashSetOfPosets<T> res = new ExtHashSetOfPosets<T>(this);
    Iterator<Poset<T>> i;

    if(other!=null) {
        i = other.iterator();
        while(i.hasNext()) {
            res.add(i.next());
        }
    }

    return res;
    }

}
