package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Implementation of a Quasi Ordered Set.
 *
 * Invoke the method fix() to indicate that you have finished updating
 * this Qoset -- otherwise isGreater(s, t) may erroneously return false.
 * Details:
 * {@see Qoset.fix()}
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class Qoset<T> extends OrderedSet<T> {

    private boolean[] equiv;
    /* equiv[i + size*j] == true iff elem_i and elem_j are equivalent */

    private boolean[] minimal;
    /* minimal[i] == true iff elem_i is a minimal element */

    /* constructors */

    private Qoset(List<T> set) {
        this.set = new ArrayList<T>(set);
        this.size = this.set.size();
        this.relation = new boolean[this.size*this.size];
        this.equiv = new boolean[this.size*this.size];
        this.minimal = new boolean[this.size];
        for(int i=0; i<this.size*this.size; i++) {
            this.relation[i] = false;
            this.equiv[i] = false;
        }
        for(int i=0; i<this.size; i++) {
            /* elem_i and elem_i are equivalent */
            this.equiv[i + this.size*i] = true;
            /* no element is minimal */
            this.minimal[i] = false;
        }
    }

    /** Creates a new instance of <code>Qoset</code>.
     * @param set   the set that should be partially ordered
     */
    static public <U> Qoset<U> create(Collection<U> set) {
        return new Qoset<U>(new ArrayList<U>(set));
    }

    /** Creates a new instance of <code>Qoset</code>.
     */
    static public <U> Qoset<U> create() {
        return new Qoset<U>(new ArrayList<U>());
    }

    /** Returns a deep copy of this Object.
     */
    public Qoset<T> deepcopy() {
        Qoset<T> p = new Qoset<T>(this.set);
        System.arraycopy(this.relation, 0, p.relation, 0, this.size*this.size);
        System.arraycopy(this.equiv, 0, p.equiv, 0, this.size*this.size);
        System.arraycopy(this.minimal, 0, p.minimal, 0, this.size);
        return p;
    }


    /** Add <code>l</code> > <code>r</code> to the qoset
     */
    @Override
    public void setGreater(T l, T r) throws OrderedSetException {
        assert (l != null);
        assert (r != null);
        int indexL, indexR;

        indexL = this.set.indexOf(l);
        indexR = this.set.indexOf(r);

        /* is l minimal? */
        if(this.minimal[indexL]) {
            throw new QosetException("can't set " + l + " greater than " + r +
                    " since " + l + " is minimal");
        }

        /* take care of equivalent elements as well */
        int i, j;
        for(i=0; i<this.size; i++) {
            if(this.equiv[indexL + this.size*i]) {
                /* l and elem_i are equivalent */
                for(j=0; j<this.size; j++) {
                    if(this.equiv[indexR + this.size*j]) {
                        /* r and elem_j are equivalent
                         * ==> set elem_i > elem_j
                         */
                        this.relation[i + this.size*j] = true;
                    }
                }
            }
        }

        this.calculateTransitiveClosure();
    }

    /** Set <code>o</code> as the minimal element of this poset, i.e.
     * <code>o</code> is smaller than all <code>r != o</code>.
     * An atempt to set an element smaller than a minimal element will result
     * in an exception.
     */
    public void setMinimal(T o) throws QosetException {
        int index = this.set.indexOf(o);

        /* check if minimality is possible */
        for(int i=0; i<this.size; i++) {
            if(this.relation[index + this.size*i]) {
                throw new QosetException("Can't set " + o + " minimal since it"
                        + " is greater than " + this.set.get(i));
            }
        }

        /* get some other minimal element */
        T minObj = null;
        for(int i=0; i<this.size; i++) {
            if(this.minimal[i]) {
                minObj = this.set.get(i);
            }
        }
        if(minObj != null) {
            this.setEquivalent(o, minObj);
        }

        /* update minimal */
        this.minimal[index] = true;

        /* all equivalent elements are minimal as well */
        for(int i = 0; i<this.size; i++) {
            if(this.equiv[index + this.size*i]) {
                this.minimal[i] = true;
            }
        }

        /* no need for cycle check */
    }

    /** Is <code>o</code> a minimal element?
     */
    public boolean isMinimal(T o) {
        return this.minimal[this.set.indexOf(o)];
    }

    /** Returns <code>true</code> iff <code>l</code> and <code>r</code> are
     * equivalent in this qoset.
     */
    public boolean areEquivalent(T l, T r) {
        return this.equiv[this.set.indexOf(l) + this.size*this.set.indexOf(r)];
    }

    public boolean checkEquivalent() {
        boolean allOk = true;
        for(int i=0; i<this.size; i++) {
            for(int j=0; j<this.size; j++) {
                for(int k=0; k<this.size; k++) {
                    if (this.equiv[i+this.size*k] && this.equiv[j+this.size*k] && !(this.equiv[i+this.size*j] && this.equiv[j+this.size*i])) {
                        allOk = false;
                    }
                }
            }
        }
        return allOk;
    }

    /** Return the list of all pairs (t, u) with t ~ u.
     */
    public List<Pair<T, T>> getEquivalences() {

        List<Pair<T, T>> result = new ArrayList<Pair<T, T>>();
        for (T t : this.set) {
            for (T u : this.set) {
                if (t != u && this.areEquivalent(t, u)) {
                    result.add(new Pair<T, T>(t, u));
                }
            }
        }
        return result;
    }

    /** Add <code>l</code> equivalent to <code>r</code> to this qoset.
     */
    @Override
    public void setEquivalent(T l, T r) throws QosetException {
        int indexL = this.set.indexOf(l);
        int indexR = this.set.indexOf(r);
        int i, j;

        this.equiv[indexL + this.size*indexR] = true;
        this.equiv[indexR + this.size*indexL] = true;

        if(this.minimal[indexL] || this.minimal[indexR]) {
            this.minimal[indexL] = true;
            this.minimal[indexR] = true;
        }

        /* elements that are equivalent to l have to be equivalent to all
         * elements that are equivalent to r and vice versa
         */
        for(int k=0; k<this.size; k++) {
            for(i=0; i<this.size; i++) {
                if (this.equiv[i+this.size*k]) {
                    for(j=0; j<this.size; j++) {
                        if (this.equiv[j+this.size*k]) {
                            this.equiv[i+this.size*j] = true;
                        }
                    }
                }
            }
        }
        this.checkEquivalent();

        /* elem_i > l ==> set elem_i > h for all h that are equivalent to r */
        for(i=0; i<this.size; i++) {
            if(this.relation[i + this.size*indexL]) {
                /* elem_i > l */
                for(j=0; j<this.size; j++) {
                    if(this.equiv[indexR + this.size*j]) {
                        /* r and elem_j are equivalent */
                        this.relation[i + this.size*j] = true;
                    }
                }
            }
        }
        /* elem_i > r ==> set elem_i > h for all h that are equivalent to l */
        for(i=0; i<this.size; i++) {
            if(this.relation[i + this.size*indexR]) {
                /* elem_i > r */
                for(j=0; j<this.size; j++) {
                    if(this.equiv[indexL + this.size*j]) {
                        /* r and elem_j are equivalent */
                        this.relation[i + this.size*j] = true;
                    }
                }
            }
        }
        /* l > elem_i ==> set h > elem_i for all h that are equivalent to r */
        for(i=0; i<this.size; i++) {
            if(this.relation[indexL + this.size*i]) {
                /* l > elem_i */
                for(j=0; j<this.size; j++) {
                    if(this.equiv[indexR + this.size*j]) {
                        /* r and elem_j are equivalent */
                        this.relation[j + this.size*i] = true;
                    }
                }
            }
        }
        /* r > elem_i ==> set h > elem_i for all h that are equivalent to l */
        for(i=0; i<this.size; i++) {
            if(this.relation[indexR + this.size*i]) {
                /* r > elem_i */
                for(j=0; j<this.size; j++) {
                    if(this.equiv[indexL + this.size*j]) {
                        /* l and elem_j are equivalent */
                        this.relation[j + this.size*i] = true;
                    }
                }
            }
        }

        this.calculateTransitiveClosure();
    }

    /** Extends the set of this qoset to include newSet as well.
     */
    public Qoset<T> extendSet(List<T> newSet) {
        List<T> newVector = new ArrayList<T>(this.set);
        newVector.addAll(newSet);
        int newSize = newVector.size();
        Qoset<T> res = Qoset.create(newVector);

        /* strict part and equivalences */
        for(int i=0; i<this.size; i++) {
            for(int j=0; j<this.size; j++) {
                if(this.relation[i + this.size*j]) {
                    res.relation[i + newSize*j] = true;
                }
                if(this.equiv[i + this.size*j]) {
                    res.equiv[i + newSize*j] = true;
                }
            }
        }
        /* minimal elements */
        for(int i=0; i<this.size; i++) {
            if(this.minimal[i]) {
                res.minimal[i] = true;
            }
        }

        return res;
    }

    /** Removes oldSet from this qoset.
     */
    public Qoset<T> collapseSet(List<T> oldSet) {
        List<T> newVector = new ArrayList<T>(this.set);
        newVector.removeAll(oldSet);
        int newSize = newVector.size();
        Qoset<T> res = Qoset.create(newVector);

        int mapping[] = new int[newSize];
        int count = 0;
        Iterator it = newVector.iterator();
        while (it.hasNext()) {
            Object neW = it.next();
            int position = this.set.indexOf(neW);
            mapping[count] = position;
            count = count+1;
        }

        /* strict part */
        for(int i=0; i<newSize; i++) {
            for(int j=0; j<newSize; j++) {
                if(this.relation[mapping[i] + this.size*mapping[j]]) {
                    res.relation[i + newSize*j] = true;
                }
                if(this.equiv[mapping[i] + this.size*mapping[j]]) {
                    res.equiv[i + newSize*j] = true;
                }
            }
        }

        for (int i=0; i<newSize; i++) {
            if (this.minimal[mapping[i]]) {
                res.minimal[i] = true;
            }
        }

        return res;
    }


    /** Merges the qoset represented by this object with the qoset
     * <code>other</code> and returns a new qoset.
     */
    public Qoset<T> mergeSlow(Qoset<T> other) throws QosetException {
        if (this.size == 0) {
            return other.deepcopy();
        } else if (other.size == 0) {
            return this.deepcopy();
        }
        if ((this.size == other.size) && (this.set.equals(other.set))) {
            return this.merge(other);
        }
        Set<T> set = new HashSet<T>(this.set);
        set.addAll(other.set);
        List<T> vSet = new ArrayList<T>(set);

        int[] thisInd = new int[this.size];
        int[] otherInd = new int[other.size];

        for(int i=0; i<this.size; i++) {
            thisInd[i] = vSet.indexOf(this.set.get(i));
        }

        for(int i=0; i<other.size; i++) {
            otherInd[i] = vSet.indexOf(other.set.get(i));
        }

        Qoset<T> res = Qoset.create(new ArrayList<T>(set));
        for (int i = 0; i < this.size; i++) {
            for (int j = 0; j < this.size; j++) {
                if (this.relation[i + this.size * j]) {
                    res.relation[thisInd[i] + res.size * thisInd[j]] = true;
                }
                if (this.equiv[i + this.size * j]) {
                    res.equiv[thisInd[i] + res.size * thisInd[j]] = true;
                }
            }
            if (this.minimal[i]) {
                res.minimal[thisInd[i]] = true;
            }
        }
        for (int i = 0; i < other.size; i++) {
            for (int j = 0; j < other.size; j++) {
                if (other.relation[i + other.size * j]) {
                    res.relation[otherInd[i] + res.size * otherInd[j]] = true;
                }
                if (other.equiv[i + other.size * j]) {
                    res.equiv[otherInd[i] + res.size * otherInd[j]] = true;
                }
            }
            if (other.minimal[i]) {
                res.minimal[otherInd[i]] = true;
            }
        }
        res.updateEquivalences();
        res.calculateTransitiveClosure();
        for(int i=0; i<res.size; i++) {
            if(res.minimal[i]) {
                for(int j=0; j<res.size; j++) {
                    if(res.relation[i + res.size*j]) {
                        throw new QosetException("the minimal element " + res.set.get(i)
                                + " is greater than " + res.set.get(j));
                    }
                }
            }
        }
        return res;
    }

    /** Merges the qoset represented by this object with the qoset
     * <code>other</code> and returns a new qoset.
     */
    public Qoset<T> merge(Qoset<T> other) throws QosetException {
        if(this.size!=other.size) {
            throw new QosetException("Incompatible qosets in merge");
        }
        Qoset<T> res = Qoset.create(this.set);
        for(int i=0; i<this.size*this.size; i++) {
            if(this.relation[i] || other.relation[i]) {
                res.relation[i] = true;
            }
            if(this.equiv[i] || other.equiv[i]) {
                res.equiv[i] = true;
            }
        }
        for(int i=0; i<this.size; i++) {
            if(this.minimal[i] || other.minimal[i]) {
                res.minimal[i] = true;
            }
        }

        res.updateEquivalences();
        res.calculateTransitiveClosure();
        for(int i=0; i<this.size; i++) {
            if(res.minimal[i]) {
                for(int j=0; j<this.size; j++) {
                    if(res.relation[i + this.size*j]) {
                        throw new QosetException("the minimal element " + this.set.get(i)
                                + " is greater than " + this.set.get(j));
                    }
                }
            }
        }

        return res;
    }

    /** Intersects the qoset represented by this object with the qoset
     * <code>other</code> and returns a new qoset.
     */
    public Qoset<T> intersect(Qoset<T> other) throws QosetException {
        if(this.size!=other.size) {
            throw new QosetException("Incompatible qosets in intersect");
        }
        Qoset<T> res = Qoset.create(this.set);
        for(int i=0; i<this.size*this.size; i++) {
            if(this.relation[i] && other.relation[i]) {
                res.relation[i] = true;
            }
            if(this.equiv[i] && other.equiv[i]) {
                res.equiv[i] = true;
            }
        }
        for(int i=0; i<this.size; i++) {
            if(this.minimal[i] && other.minimal[i]) {
                res.minimal[i] = true;
            }
        }

        res.calculateTransitiveClosure();
        return res;
    }

    /** Returns <code>true</code> if the qoset represented by this object
     * is contained in the qoset <code>other</code>, <code>false</code>
     * otherwise.
     * A qoset <code>P</code> is contained in a qoset <code>Q</code>
     * iff <code>f</code> > <code>g</code> in <code>P</code> implies
     * <code>f</code> > <code>g</code> in <code>Q</code> for all
     * <code>f</code>, <code>g</code>.
     */
    public boolean isContainedIn(Qoset other) throws QosetException {
        if(this.size!=other.size) {
            throw new QosetException("Incompatible qosets in isContainedIn");
        }
        for(int i=0; i<this.size*this.size; i++) {
            if(this.relation[i] && !other.relation[i]) {
                return false;
            }
            if(this.equiv[i] && !other.equiv[i]) {
                return false;
            }
        }
        for(int i=0; i<this.size; i++) {
            if(this.minimal[i] && !other.minimal[i]) {
                return false;
            }
        }

        return true;
    }

    /** Returns <code>true</code> if this qoset and the qoset
     * <code>o</code> contain the same relation, <code>false</code>
     * otherwise.
     */
    @Override
    public boolean equals(Object o) {
        Qoset other;
        try {
            other = (Qoset)o;
        }
        catch(ClassCastException e) {
            return false;
        }
        if(this.size!=other.size) {
            return false;
        }
        else {
            for(int i=0; i<this.size*this.size; i++) {
                if(this.relation[i] != other.relation[i]) {
                    return false;
                }
                if(this.equiv[i] != other.equiv[i]) {
                    return false;
                }
            }
            for(int i=0; i<this.size; i++) {
                if(this.minimal[i] != other.minimal[i]) {
                    return false;
                }
            }
            return true;
        }
    }

    private void calculateTransitiveClosure() throws QosetException {
        for(int y=0; y<this.size; y++) {
            for(int x=0; x<this.size; x++) {
                if(this.relation[x + this.size*y]) {
                    for(int j=0; j<this.size; j++) {
                        if(this.relation[y + this.size*j]) {
                            this.relation[x + this.size*j] = true;
                        }
                    }
                }
            }
        }
        this.cycleCheck();
    }

    private void cycleCheck() throws QosetException {
        for(int i=0; i<this.size; i++) {
            if(this.relation[i + this.size*i]) {
                StringBuffer excep = new StringBuffer("Exception: ");
                excep.append(this.set.get(i));
                excep.append(" > ");
                excep.append(this.set.get(i));
                throw new QosetException(excep.toString());
            }
        }
    }

    /* updates relation to be consistent with equiv */
    private void updateEquivalences() {
        int i, j, k;
        /* minimality */
        for(i=0; i<this.size; i++) {
            for(j=0; j<this.size; j++) {
                if(i!=j && this.equiv[i + this.size*j]) {
                    if(this.minimal[i] || this.minimal[j]) {
                        this.minimal[i] = true;
                        this.minimal[j] = true;
                    }
                }
            }
        }
        for(i=0; i<this.size; i++) {
            for(j=0; j<this.size; j++) {
                if(i!=j && this.minimal[i] && this.minimal[j]) {
                    this.equiv[i + this.size*j] = true;
                    this.equiv[j + this.size*i] = true;
                }
            }
        }
        /* equivalences */
        for(i=0; i<this.size; i++) {
            for(j=0; j<this.size; j++) {
                if(i!=j && this.equiv[i + this.size*j]) {
                    for(k=0; k<this.size; k++) {
                        if(this.equiv[i + this.size*k] || this.equiv[j + this.size*k]) {
                            this.equiv[i + this.size*k] = true;
                            this.equiv[j + this.size*k] = true;
                        }
                    }
                }
            }
        }
        /* update strict part as well */
        for(i=0; i<this.size; i++) {
            for(j=0; j<this.size; j++) {
                if(i!=j && this.equiv[i + this.size*j]) {
                    for(k=0; k<this.size; k++) {
                        if(this.relation[i + this.size*k] || this.relation[j + this.size*k]) {
                            this.relation[i + this.size*k] = true;
                            this.relation[j + this.size*k] = true;
                        }
                    }
                }
            }
        }
    }

    /**
     * Sets the equivalence class of minimal elements smaller than any other
     * equivalence class. As a consequence, it will not be possible to add
     * any further elements e to the equivalence class of minimal elements
     * (if it was non-empty before, as witnessed by some minimal element f).
     * The reason is that then e would be both equivalent to and greater
     * than f, which would imply that e is greater than e -- contradiction!
     *
     * For this reason, the fact that minimal elements are smaller than
     * non-minimal elements is represented explicitly only after this method
     *
     *
     * Thus, you should call this method before invoking isGreater(),
     * otherwise isGreater() will not take into account that minimal elements
     * are smaller than non-minimal elements. Use this method to indicate
     * that you have finished updating this Qoset.
     */
    public void fix() throws OrderedSetException {
        int minIndex = -1;
        for(int i=0; i<this.size; i++) {
            if(this.minimal[i]) {
                minIndex = i;
            }
        }
        if(minIndex != -1) {
            for(int i=0; i<this.size; i++) {
                if(!this.minimal[i]) {
                    this.setGreater(this.set.get(i), this.set.get(minIndex));
                }
            }
            this.calculateTransitiveClosure();
        }
    }

    public boolean isTrivial(){
        return this.toPoset().isTrivial();
    }

    public List<List<List<T>>> topSort() {
        return this.toPoset().topSort();
    }

    @Override
    public String export(Export_Util eu) {
        return this.toPoset().export(eu);
    }

    @Override
    public String toHashString() {
        StringBuffer result = new StringBuffer();
        boolean[] tmp = new boolean[this.size];
        int i, j;

        for(i=0; i<this.size; i++) {
            tmp[i] = false;
        }

        result.append("Equivalence classes:\n");
        for(i=0; i<this.size; i++) {
            if(!tmp[i]) {
                // elem_i was not yet printed
                result.append("{");
                result.append(this.set.get(i));
                tmp[i] = true;
                for(j=0; j<this.size; j++) {
                    if(i!=j && this.equiv[i + this.size*j]) {
                        result.append(", " + this.set.get(j));
                        tmp[j] = true;
                    }
                }
                result.append("}\n");
            }
        }
        result.append("Strict part:\n");
        for(i=0; i<this.size; i++) {
            result.append(this.set.get(i));
            result.append(" >");
            boolean fst = true;
            for(j=0; j<this.size; j++) {
                if(this.relation[i + this.size*j]) {
                    if(!fst) {
                        result.append(", ");
                    }
                    else {
                        result.append(" ");
                        fst = false;
                    }
                    result.append(this.set.get(j));
                }
            }
            if(i<this.size-1) {
                result.append("\n");
            }
        }

        return result.toString();
    }

    /** Returns a string representation of this object.
     */
    @Override
    public String toString() {
        return this.toPoset().toString();
    }

    @Override
    public String toDOT() {
        return this.toPoset().toDOT();
    }

    private Poset<List<T>> toPoset(){
        List<List<T>> tmpsig = new ArrayList<List<T>>();
        boolean tmp[] = new boolean[this.size];
        Map<Integer,List<T>> map = new HashMap<Integer,List<T>>();
        int i,j;
        for (i = 0; i < this.size; i++) {
            tmp[i] = false;
        }
        for (i = 0; i < this.size; i++) {
            if(!tmp[i]) {
                List<T> tmp2 = new ArrayList<T>();
                tmp2.add(this.set.get(i));
                map.put(Integer.valueOf(i), tmp2);
                tmp[i] = true;
                for(j=0; j<this.size; j++) {
                    if(i!=j && this.equiv[i + this.size*j]) {
                        tmp2.add(this.set.get(j));
                        map.put(Integer.valueOf(j), tmp2);
                        tmp[j] = true;
                    }
                }
                tmpsig.add(tmp2);
            }
        }
        Poset<List<T>> temp = Poset.create(tmpsig);
        for (i = 0; i < this.size; i++) {
            if(this.minimal[i]) {
                try {
                    temp.setMinimal(map.get(Integer.valueOf(i)));
                }
                catch(PosetException e) {
                }
            }
            for (j = 0; j < this.size; j++) {
                if (this.relation[i+this.size*j]) {
                    try {
                        temp.setGreater(map.get(Integer.valueOf(i)), map.get(Integer.valueOf(j)));
                    } catch (OrderedSetException e) {}
                }
            }
        }
        return temp;
    }

    /** Returns the qoset induced by newSet.
     */
    public Qoset<T> project(Collection<T> newSet) {
        List<T> newVector = new ArrayList<T>(this.set);
        newVector.retainAll(newSet);
        int newSize = newVector.size();
        Qoset<T> res = Qoset.create(newVector);

        int mapping[] = new int[newSize];
        int count = 0;
        Iterator it = newVector.iterator();
        while (it.hasNext()) {
            Object neW = it.next();
            int position = this.set.indexOf(neW);
            mapping[count] = position;
            count = count+1;
        }

        /* strict part */
        for(int i=0; i<newSize; i++) {
            for(int j=0; j<newSize; j++) {
                if(this.relation[mapping[i] + this.size*mapping[j]]) {
                    res.relation[i + newSize*j] = true;
                }
                if(this.equiv[mapping[i] + this.size*mapping[j]]) {
                    res.equiv[i + newSize*j] = true;
                }
            }
        }

        for (int i=0; i<newSize; i++) {
            if (this.minimal[mapping[i]]) {
                res.minimal[i] = true;
            }
        }

        return res;
    }

    @Override
    public Map<T,Integer> getTopSortMap() {
        Set<Integer> visited = new LinkedHashSet<Integer>();
        List<Set<Integer>> list = new ArrayList<Set<Integer>>();

        for (int i = 0; i < this.size; i++) {
            if (!visited.contains(i)) {
                this.getTopSortMapVisit(i, visited, list);
            }
        }
        Map<T,Integer> map = new LinkedHashMap<T,Integer>();
        for (int i = 0; i < list.size(); i++) {
            for (int j : list.get(i)) {
                map.put(this.set.get(j), i);
            }
        }
        if (Globals.useAssertions) {
            for (int i = 0; i < this.size; i++) {
                for (int j = 0; j < this.size; j++) {
                    if (this.relation[i+this.size*j]) {
                        assert map.get(this.set.get(i)) > map.get(this.set.get(j));
                    }
                    if (this.equiv[i+this.size*j]) {
                        assert map.get(this.set.get(i)).intValue() == map.get(this.set.get(j)).intValue();
                    }
                }
            }
        }
        return map;
    }

    private void getTopSortMapVisit(int i, Set<Integer> visited, List<Set<Integer>> list) {
        for (int j = 0; j < this.size; j++) {
            if (this.relation[i+this.size*j] && !visited.contains(j)) {
                this.getTopSortMapVisit(j, visited, list);
            }
        }
        Set<Integer> set = new LinkedHashSet<Integer>();
        for (int j = 0; j < this.size; j++) {
            if (this.equiv[i+this.size*j]) {
                set.add(j);
            }
        }
        list.add(set);
        visited.addAll(set);
    }

}
