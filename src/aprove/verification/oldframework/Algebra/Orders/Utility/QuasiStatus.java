package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.prooftree.Export.Utility.*;

/** Encapsulates quasi precedence and quasi status map.
 *
 *  @author  Stephan Falke
 *  @version $Id$
 */

public class QuasiStatus<T> implements Exportable, SizeMeasure {
    private Qoset<T> precedence;
    private StatusMap<T> statusMap;


    //  Default constructor should only be used publicly by XML serialization.
    public QuasiStatus() {

    }

    /* constructros */

    private QuasiStatus(Qoset<T> precedence, StatusMap<T> statusMap) {
        this.precedence = precedence.deepcopy();
        this.statusMap = statusMap.deepcopy();
    }

    /** Returns a new instance of <code>QuasiStatus</code>.
     * @param precedence   the quasi precedence to be encapsulated
     * @param statusMap    the quasi status map to be encapsulated
     */
    public static <U> QuasiStatus<U> create(Qoset<U> precedence, StatusMap<U> statusMap) {
        return new QuasiStatus<U>(precedence, statusMap);
    }

    /** Returns a new instance of <code>QuasiStatus</code> containing empty
     * precedence and status map.
     * @param set   the set on which this quasi status operates
     */
    public static <U> QuasiStatus<U> create(List<U> set) {
        return new QuasiStatus<U>(Qoset.create(set), StatusMap.create(set));
    }

    /** Returns a new instance of <code>QuasiStatus</code> containing empty
     * precedence and status map.
     */
    public static <U> QuasiStatus<U> create() {
        List<U> set = new ArrayList<U>();
        return new QuasiStatus<U>(Qoset.create(set), StatusMap.create(set));
    }

    /** Returns the set on which this quasi status operates.
     */
    public List<T> getSet() {
        return this.precedence.getSet();
    }

    /** Returns the quasi precedence encapsulated by this object.
     */
    public Qoset<T> getPrecedence() {
        return this.precedence;
    }

    /** Returns the quasi status map encapsulated by this object.
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
     * quasi status, <code>false</code> otherwise.
     */
    public boolean hasPermutation(T o) {
        return this.statusMap.hasPermutation(o);
    }

    /** Returns <code>true</code> if <code>o</code> has multiset status in
     * this quasi status, </code>false</code> otherwise.
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

    /** Sets <code>o</code> to be smaller than any other element.
     */
    public void setMinimal(T o) throws QuasiStatusException {
        try {
            this.precedence.setMinimal(o);
        }
        catch(QosetException e) {
            throw new QuasiStatusException(e.getMessage());
        }
    }

    /** Is <code>o</code> a minimal element?
     */
    public boolean isMinimal(T o) {
        return this.precedence.isMinimal(o);
    }

    /** Add <code>l</code> > <code>r</code> to the status.
     */
    public void setGreater(T l, T r) throws QuasiStatusException {
        try {
            this.precedence.setGreater(l, r);
        }
        catch(OrderedSetException e) {
            throw new QuasiStatusException(e.getMessage());
        }
    }

    /** Sets <code>l</code> and <code>r</code> to be equivalent in this quasi
     * status.
     */
    public void setEquivalent(T l, T r) throws QuasiStatusException {
        try {
            this.precedence.setEquivalent(l, r);
        }
        catch(QosetException e) {
            throw new QuasiStatusException(e.getMessage());
        }
    }

    /** Returns <code>true</code> if <code>l</code> > <code>r</code> in
     * this quasi status, <code>false</code> otherwise.
     */
    public boolean isGreater(T l, T r) {
        return this.precedence.isGreater(l, r);
    }

    /** Returns <code>true</code> if <code>l</code> and <code>r</code> are
     * equivalent in this quasi status, <code>false</code> otherwise.
     */
    public boolean areEquivalent(T l, T r) {
        return this.precedence.areEquivalent(l, r);
    }


    /** Returns a deep copy of this object.
     */
    public QuasiStatus<T> deepcopy() {
        return new QuasiStatus<T>(this.precedence, this.statusMap);
    }

    /** Merges this quasi status with the quasi status <code>other</code> and
     * returns a new quasi status.
     */
    public QuasiStatus<T> mergeSlow(QuasiStatus<T> other) throws QuasiStatusException {
        QuasiStatus<T> res;
        try {
            res = QuasiStatus.create(this.precedence.mergeSlow(other.precedence),
                    this.statusMap.merge(other.statusMap));
        }
        catch(Exception e) {
            throw new QuasiStatusException("Incompatible quasi statuses in merge");
        }

        return res;
    }

    /** Merges this quasi status with the quasi status <code>other</code> and
     * returns a new quasi status.
     */
    public QuasiStatus<T> merge(QuasiStatus<T> other) throws QuasiStatusException {
        QuasiStatus<T> res;
        try {
            res = QuasiStatus.create(this.precedence.merge(other.precedence),
                    this.statusMap.merge(other.statusMap));
        }
        catch(Exception e) {
            throw new QuasiStatusException("Incompatible quasi statuses in merge");
        }

        return res;
    }

    /** Intersects this quasi status with the quasi status <code>other</code>
     * and returns a new quasi status.
     */
    public QuasiStatus<T> intersect(QuasiStatus<T> other) throws QuasiStatusException {
        QuasiStatus<T> res;
        try {
            res = QuasiStatus.create(this.precedence.intersect(other.precedence),
                    this.statusMap.intersect(other.statusMap));
        }
        catch(Exception e) {
            throw new QuasiStatusException("Incompatible quasi statuses in intersect");
        }

        return res;
    }

    /** Returns <code>true</code> is this quasi status is contained in the
     * quasi status <code>other</code>.
     * A quasi status <code>M</code> is contained in a quasi status
     * <code>N</code> iff <code>M</code>'s quasi precedence is contained in
     * <code>N</code>'s quasi precedence and <code>M</code>'s quasi status map
     * is contained in <code>N</code>'s quasi status map.
     */
    public boolean isContainedIn(QuasiStatus<T> other) throws QuasiStatusException {
        boolean res;
        try {
            res = this.precedence.isContainedIn(other.precedence) &&
            this.statusMap.isContainedIn(other.statusMap);
        }
        catch(Exception e) {
            throw new QuasiStatusException("Incompatible quasi statuses in isContainedIn");
        }

        return res;
    }

    /** Returns <code>true</code> if this object and the object
     * <code>o</code> represent the same quasi status, <code>false</code>
     * otherwise.
     */
    @Override
    public boolean equals(Object o) {
        QuasiStatus other;
        try {
            other = (QuasiStatus)o;
        }
        catch(ClassCastException e) {
            return false;
        }

        return this.precedence.equals(other.precedence) &&
        this.statusMap.equals(other.statusMap);
    }

    /** Returns a string representing the object.
     */
    @Override
    public String toString() {
        StringBuffer temp = new StringBuffer();
        temp.append("Quasi precedence:\n");
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
        temp.append("Quasi precedence:\n");
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
    public int hashCode() {
        return this.toHashString().hashCode();
    }

    public void fix() throws QuasiStatusException {
        try {
            this.precedence.fix();
        } catch (OrderedSetException e) {
            throw new QuasiStatusException(e.getMessage());
        }
    }

    public QuasiStatus<T> project(Collection<T> newSet) {
        QuasiStatus<T> res = QuasiStatus.create();
        res.precedence = this.precedence.project(newSet);
        res.statusMap = this.statusMap.project(newSet);
        return res;
    }

    @Override
    public String export(Export_Util eu) {
        return "Quasi-Precedence: "+this.precedence.export(eu) + eu.cond_linebreak()+
            "Status: " + this.statusMap.export(eu)+eu.cond_linebreak();
    }



    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setPrecedence(Qoset<T> precedence) {
        this.precedence = precedence;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setStatusMap(StatusMap<T> statusMap) {
        this.statusMap = statusMap;
    }

    @Override
    public int getSizeMeasure() {
        return (this.precedence.getSizeMeasure() + this.statusMap.getSizeMeasure());
    }

}
