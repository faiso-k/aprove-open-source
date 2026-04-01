package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.prooftree.Export.Utility.*;

/** Encapsulates precedence and status map.
 *
 *  @author  Peter Schneider-Kamp, Stephan Falke
 *  @version $Id$
 */

public class Status<T> implements Exportable, HTML_Able, LaTeX_Able, SizeMeasure {
    private Poset<T> precedence;
    private StatusMap<T> statusMap;

    /* constructros */

    private Status(Poset<T> precedence, StatusMap<T> statusMap) {
        this.precedence = precedence.deepcopy();
        this.statusMap = statusMap.deepcopy();
    }

    /** Returns a new instance of <code>Status</code>.
     * @param precedence   the precedence to be encapsulated
     * @param statusMap    the status map to be encapsulated
     */
    public static <U> Status<U> create(Poset<U> precedence, StatusMap<U> statusMap) {
        return new Status<U>(precedence, statusMap);
    }

    /** Returns a new instance of <code>Status</code> containing empty
     * precedence and status map.
     * @param set   the set on which this status operates
     */
    public static <U> Status<U> create(List<U> set) {
        return new Status<U>(Poset.create(set), StatusMap.create(set));
    }

    /** Returns a new instance of <code>Status</code> containing empty
     * precedence and status map.
     */
    public static <U> Status<U> create() {
        List<U> set = new ArrayList<U>();
        return new Status<U>(Poset.create(set), StatusMap.create(set));
    }

    /** Returns the set on which this status operates.
     */
    public List<T> getSet() {
        return this.precedence.getSet();
    }

    /** Returns the precedence encapsulated by this object.
     */
    public Poset<T> getPrecedence() {
        return this.precedence;
    }

    /** Returns the status map encapsulated by this object.
     */
    public StatusMap<T> getStatusMap() {
        return this.statusMap;
    }

    /** Assigns permutation <code>perm</code> to object <code>o</code>.
     */
    public void assignPermutation(T o, Permutation perm) {
        this.statusMap.assignPermutation(o, perm);
    }

    /** Assign multiset status to object <code>o</code>.
     */
    public void assignMultisetStatus(T o) {
        this.statusMap.assignMultisetStatus(o);
    }

    /** Assign flat status to object <code>o</code>.
     */
    public void assignFlatStatus(T o) {
        this.statusMap.assignFlatStatus(o);
    }


    /** Returns <code>o</code>'s permutation.
     */
    public Permutation getPermutation(T o) {
        return this.statusMap.getPermutation(o);
    }

    /** Returns <code>true</code> if <code>o</code> has a permutation in this
     * status, <code>false</code> otherwise.
     */
    public boolean hasPermutation(T o) {
        return this.statusMap.hasPermutation(o);
    }

    /** Returns <code>true</code> if <code>o</code> has multiset status in
     * this status, </code>false</code> otherwise.
     */
    public boolean hasMultisetStatus(T o) {
        return this.statusMap.hasMultisetStatus(o);
    }

    /** Returns <code>true</code> if <code>o</code> has flat status in
     * this status, </code>false</code> otherwise.
     */
    public boolean hasFlatStatus(T o) {
        return this.statusMap.hasFlatStatus(o);
    }

    /** Returns <code>true</code> if <code>o</code> has a status,
     * </code>false</code> otherwise.
     */
    public boolean hasEntry(T o) {
        return this.statusMap.hasEntry(o);
    }

    /** Add <code>l</code> > <code>r</code> to the status.
     */
    public void setGreater(T l, T r) throws StatusException {
        try {
            this.precedence.setGreater(l, r);
        }
        catch(OrderedSetException e) {
            throw new StatusException(e.getMessage());
        }
    }

    /** Sets <code>o</code> to be smaller than any other element.
     */
    public void setMinimal(T o) throws StatusException {
        try {
            this.precedence.setMinimal(o);
        }
        catch(PosetException e) {
            throw new StatusException(e.getMessage());
        }
    }

    /** Returns <code>true</code> if <code>l</code> > <code>r</code> in
     * this status, <code>false</code> otherwise.
     */
    public boolean isGreater(T l, T r) {
        return this.precedence.isGreater(l, r);
    }

    /** Returns a deep copy of this object.
     */
    public Status<T> deepcopy() {
        return new Status<T>(this.precedence, this.statusMap);
    }

    /** Merges this status with the status <code>other</code> and
     * returns a new status.
     */
    public Status<T> mergeSlow(Status<T> other) throws StatusException {
        Status<T> res;
        try {
            res = Status.create(this.precedence.mergeSlow(other.precedence),
                    this.statusMap.merge(other.statusMap));
        }
        catch(Exception e) {
            throw new StatusException("Incompatible statuses in merge");
        }

        return res;
    }

    /** Merges this status with the status <code>other</code> and
     * returns a new status.
     */
    public Status<T> merge(Status<T> other) throws StatusException {
        Status<T> res;
        try {
            res = Status.create(this.precedence.merge(other.precedence),
                    this.statusMap.merge(other.statusMap));
        }
        catch(Exception e) {
            throw new StatusException("Incompatible statuses in merge");
        }

        return res;
    }

    /** Intersects this status with the status <code>other</code>
     * and returns a new status.
     */
    public Status<T> intersect(Status<T> other) throws StatusException {
        Status<T> res;
        try {
            res = Status.create(this.precedence.intersect(other.precedence),
                    this.statusMap.intersect(other.statusMap));
        }
        catch(Exception e) {
            throw new StatusException("Incompatible statuses in intersect");
        }

        return res;
    }

    /** Returns <code>true</code> is this status is contained in the status
     * <code>other</code>.
     * A status <code>M</code> is contained in a status <code>N</code>
     * iff <code>M</code>'s precedence is contained in <code>N</code>'s
     * precedence and <code>M</code>'s status map is contained in
     * <code>N</code>'s status map.
     */
    public boolean isContainedIn(Status<T> other) throws StatusException {
        boolean res;
        try {
            res = this.precedence.isContainedIn(other.precedence) &&
            this.statusMap.isContainedIn(other.statusMap);
        }
        catch(Exception e) {
            throw new StatusException("Incompatible statuses in isContainedIn");
        }

        return res;
    }

    /** Returns <code>true</code> if this object and the object
     * <code>o</code> represent the same status, <code>false</code>
     * otherwise.
     */
    @Override
    public boolean equals(Object o) {
        Status other;
        try {
            other = (Status)o;
        }
        catch(ClassCastException e) {
            return false;
        }
        return this.precedence.equals(other.precedence) &&
        this.statusMap.equals(other.statusMap);
    }


    @Override
    public String export(Export_Util eu) {
        if (eu instanceof PLAIN_Util) {
            return this.toString();
        } else if (eu instanceof HTML_Util) {
            return this.toHTML();
        } else if (eu instanceof LaTeX_Util) {
            return this.toLaTeX();
        } else {
            return this.toString();
        }
    }


    /** Returns a string representing the object.
     */
    @Override
    public String toString() {
        StringBuffer temp = new StringBuffer();
        temp.append("Precedence:\n");
        if(this.precedence!=null) {
            temp.append(this.precedence);
        }
        temp.append("\n\nStatus:\n");
        if(this.statusMap!=null) {
            temp.append(this.statusMap);
        }
        temp.append("\n");
        return temp.toString();
    }

    public String toHashString() {
        StringBuffer temp = new StringBuffer();
        temp.append("Precedence:\n");
        if(this.precedence!=null) {
            temp.append(this.precedence.toHashString());
        }
        temp.append("\n\nStatus:\n");
        if(this.statusMap!=null) {
            temp.append(this.statusMap);
        }
        temp.append("\n");
        return temp.toString();
    }

    @Override
    public String toHTML() {
        return "Precedence:<BR>" + this.precedence.toHTML()
        + "<BR>Status:<BR>" + this.statusMap.toHTML();
    }

    @Override
    public int hashCode() {
        return this.toHashString().hashCode();
    }

    public Status<T> project(Collection<T> newSet) {
        Status<T> res = Status.create();
        res.precedence = this.precedence.project(newSet);
        res.statusMap = this.statusMap.project(newSet);
        return res;
    }

    @Override
    public String toLaTeX() {
        return "Precedence:" + this.precedence.toLaTeX() + "Status:" + this.statusMap.toLaTeX();
    }

    @Override
    public int getSizeMeasure(){
        return (this.precedence.getSizeMeasure() + this.statusMap.getSizeMeasure()) ;
    }
}
