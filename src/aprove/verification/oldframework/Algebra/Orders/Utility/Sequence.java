package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;


/** Encapsulation of a sequence of m elements from {0, 1, ..., n-1}.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class Sequence {
    private int[] seq;
    private int size;


    //  Default constructor should only be used publicly by XML serialization.
    public Sequence() {

    }


    /* constructors */

    private Sequence(int[] seq) {
    this.size = seq.length;
    this.seq = new int[this.size];
    System.arraycopy(seq, 0, this.seq, 0, this.size);
    }

    /** Creates a new instance of <code>Sequence</code>.
     * @param seq   the sequence that should be encapsulated
     */
    static public Sequence create(int[] seq) {
        return new Sequence(seq);
    }

    /** Return the number at position <code>i</code> if 0 <= <code>i</code>
     *  <= m-1, <code>-1</code> otherwise.
     */
    public int get(int i) {
    if (i<0 || i>=this.size) {
        return -1;
    }
    else {
        return this.seq[i];
    }
    }

    /** Returns <code>m</code>.
     */
    public int size() {
    return this.size;
    }

    /** Returns a string representation of the object.
     */
    @Override
    public String toString() {
    StringBuffer res = new StringBuffer();

    res.append("[");
    for (int i=0; i<this.size; i++) {
        res.append(this.get(i));
        if(i<this.size-1) {
        res.append(",");
        }
    }

    res.append("]");

    return res.toString();
    }

    /** Returns <code>true</code> if the two objects represent the same
     * sequence, <code>false</code> otherwise.
     */
    @Override
    public boolean equals(Object o) {
        if (o == null) {
            return false;
        }
        Sequence other;
    try {
       other = (Sequence)o;
    }
    catch(ClassCastException e) {
        return false;
    }
    if(this.size!=other.size) {
        return false;
    }
    else {
        for(int i=0; i<this.size; i++) {
        if(this.seq[i]!=other.seq[i]) {
            return false;
        }
        }
        return true;
    }
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(this.seq);
    }

    /** Returns a deep copy of the object.
     */
    public Sequence deepcopy() {
    Sequence p = new Sequence(this.seq);
        return p;
    }


    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public int[] getSeq() {
        return this.seq;
    }


    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setSeq(int[] seq) {
        this.seq = seq;
    }


    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public int getSize() {
        return this.size;
    }


    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setSize(int size) {
        this.size = size;
    }


}
