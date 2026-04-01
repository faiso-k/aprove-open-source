/*
 * Created on Feb 24, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

/** Encapsulation of a of vector of booleans.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class BoolVector {
    private boolean[] vector;
    private int value;
    private int size;

    /* constructors */

    private BoolVector(boolean[] vector, int value) {
        this.size = vector.length;
        this.vector = new boolean[this.size];
        System.arraycopy(vector, 0, this.vector, 0, this.size);
        this.value = value;
    }

    /** Creates a new instance of <code>BoolVector</code>.
     * @param vector   the boolean array that should be encapsulated
     * @param value    an additional int to store with this vector
     */
    static public BoolVector create(boolean[] vector, int value) {
        return new BoolVector(vector, value);
    }

    /** Creates a new instance of <code>BoolVector</code> containing which elements of
     * an IntVector are not 0.
     * @param vector   an IntVector
     */
    static public BoolVector create(IntVector vector) {
        int n = vector.size();
        boolean[] tmp = new boolean[n];
        for(int i=0; i<n; i++) {
            tmp[i] = (vector.get(i) != 0);
        }
        return new BoolVector(tmp, 0);
    }

    /** Return the value of this object.
     */
    public int getValue() {
        return this.value;
    }

    /** Sets the value of this object.
     */
    public void setValue(int value) {
        this.value = value;
    }

    /** Return the value at position <code>i</code> if 0 <= <code>i</code>
     *  <= n-1, <code>true</code> otherwise.
     */
    public boolean get(int i) {
        if (i<0 || i>=this.size) {
            return true;
        }
        else {
            return this.vector[i];
        }
    }

    /** Sets the value at position <code>i</code> if 0 <= <code>i</code>
     *  <= n-1.
     */
    public void set(int i, boolean b) {
        if (i<0 || i>=this.size) {
            return;
        }
        else {
            this.vector[i] = b;
            return;
        }
    }

    /** Computes the component-wise && of two BoolVectors and returns a new object
     * where value is taken from this BoolVector.
     */
    public BoolVector conj(BoolVector other) {
        boolean[] newVec= new boolean[this.size];
        for(int i=0; i<this.size; i++) {
            newVec[i] = this.vector[i] && other.vector[i];
        }
        int newValue = this.value;
        return BoolVector.create(newVec, newValue);
    }

    /** Computes the component-wise || of two BoolVectors and returns a new object
     * where value is taken from this BoolVector.
     */
    public BoolVector disj(BoolVector other) {
        boolean[] newVec= new boolean[this.size];
        for(int i=0; i<this.size; i++) {
            newVec[i] = this.vector[i] || other.vector[i];
        }
        int newValue = this.value;
        return BoolVector.create(newVec, newValue);
    }

    /** Returns true if all entries of this BoolVector are true.
     */
    public boolean isTrue() {
        for(int i=0; i<this.size; i++) {
            if(!this.vector[i]) {
            return false;
            }
        }

        return true;
    }

    /** Returns the size of this BoolVector.
     */
    public int size() {
        return this.size;
    }

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

        res.append("] Value: " + this.value);

        return res.toString();
    }

    /** Returns <code>true</code> if the two objects represent the same
     * integers, <code>false</code> otherwise.
     */
    @Override
    public boolean equals(Object o) {
        BoolVector other;
        try {
            other = (BoolVector)o;
        }
        catch(ClassCastException e) {
            return false;
        }
        if(this.size!=other.size) {
            return false;
        }
        else {
            for(int i=0; i<this.size; i++) {
                if(this.vector[i]!=other.vector[i]) {
                    return false;
                }
            }
            return this.value==other.value;
        }
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    /** Returns a deep copy of the object.
     */
    public BoolVector deepcopy() {
        BoolVector p = new BoolVector(this.vector, this.value);
        return p;
    }

}
