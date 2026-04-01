/*
 * Created on Feb 24, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

/** Encapsulation of a of vector of integers.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class IntVector {
    private IntVector vecVal;
    private int[] vector;
    private int value;
    private int size;

    /* constructors */

    private IntVector(int[] vector, int value, IntVector vecVal) {
        this.size = vector.length;
        this.vector = new int[this.size];
        System.arraycopy(vector, 0, this.vector, 0, this.size);
        this.value = value;
        this.vecVal = vecVal;
    }

    /** Creates a new instance of <code>IntVector</code>.
     * @param vector   the integer array that should be encapsulated
     * @param value    an additional int to store with this vector
     */
    static public IntVector create(int[] vector, int value) {
        return new IntVector(vector, value, null);
    }

    /** Creates a new instance of <code>IntVector</code>.
     * @param vector   the integer array that should be encapsulated
     * @param vecVal    an additional IntVector to store with this vector
     */
    static public IntVector create(int[] vector, IntVector vecVal) {
        return new IntVector(vector, 0, vecVal);
    }

    /** Creates a new instance of <code>IntVector</code>.
     * @param vector   the integer array that should be encapsulated
     * @param value    an additional int to store with this vector
     * @param vecVal    an additional IntVector to store with this vector
     */
    static public IntVector create(int[] vector, int value, IntVector vecVal) {
        return new IntVector(vector, value, vecVal);
    }

    /** Creates a new instance of <code>IntVector</code> containing only n copies of 0.
     */
    static public IntVector createZero(int n) {
        int[] vec = new int[n];
        for(int i=0; i<n; i++) {
            vec[i] = 0;
        }
        return new IntVector(vec, 0, null);
    }

    /** Return the value of this object.
     */
    public int getValue() {
        return this.value;
    }

    /** Returns the vector of values of this object.
     */
    public IntVector getVecValue() {
        return this.vecVal;
    }

    /** Return the number at position <code>i</code> if 0 <= <code>i</code>
     *  <= n-1, <code>-1</code> otherwise.
     */
    public int get(int i) {
        if (i<0 || i>=this.size) {
            return -1;
        }
        else {
            return this.vector[i];
        }
    }

    /** Returns the last component.
     */
    public int getLast() {
        return this.vector[this.size - 1];
    }

    /** Adds to IntVectors component-wise and returns a new object.
     */
    public IntVector add(IntVector other) {
        int[] newVec= new int[this.size];
        for(int i=0; i<this.size; i++) {
            newVec[i] = this.vector[i] + other.vector[i];
        }
        int newValue = this.value + other.value;
        if(this.vecVal != null && other.vecVal != null) {
            return IntVector.create(newVec, newValue, this.vecVal.add(other.vecVal));
        }
        else {
            return IntVector.create(newVec, newValue);
        }
    }

    /** Computes the standard scalar product.
     */
    public int mult(IntVector other) {
        int res = 0;

        for(int i=0; i<this.size; i++) {
            res += this.vector[i] * other.vector[i];
        }

        return res;
    }

    /** Returns true if this IntVector is bigger than other.
     */
    public boolean isBigger(IntVector other) {
        boolean foundstrict = false;

        for(int i=0; i<this.size; i++) {
            if(other.vector[i] > this.vector[i]) {
                return false;
            }
            if(this.vector[i] != other.vector[i]) {
                foundstrict = true;
            }
        }

        return foundstrict;
    }

    /** Returns true if all entries of this IntVector are positive.
     */
    public boolean isPositive() {
        for(int i=0; i<this.size; i++) {
            if(this.vector[i] <= 0) {
                return false;
            }
        }

        return true;
    }

    /** Returns true if all entries of this IntVector are 0.
     */
    public boolean isTrivial() {
        for(int i=0; i<this.size; i++) {
            if(this.vector[i] != 0) {
            return false;
            }
        }

        return true;
    }

    /** Returns the size of this IntVector.
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
        if(this.vecVal != null) {
            res.append(" VecValue: [");
            for(int i=0; i<this.vecVal.size; i++) {
                res.append(this.vecVal.vector[i]);
                if(i!=this.vecVal.size-1) {
                    res.append(", ");
                }
                else {
                    res.append("]");
                }
            }
        }

        return res.toString();
    }

    /** Returns <code>true</code> if the two objects represent the same
     * integers, <code>false</code> otherwise.
     */
    @Override
    public boolean equals(Object o) {
        IntVector other;
        try {
            other = (IntVector)o;
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
            if(this.value!=other.value) {
                return false;
            }
            else {
                if(this.vecVal==null && other.vecVal==null) {
                    return true;
                }
                else if(this.vecVal==null || other.vecVal==null) {
                    return false;
                }
                for(int i=0; i<this.vecVal.size; i++) {
                    if(this.vecVal.vector[i] != other.vecVal.vector[i]) {
                        return false;
                    }
                }
                return true;
            }
        }
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    /** Returns a deep copy of the object.
     */
    public IntVector deepcopy() {
        IntVector p = new IntVector(this.vector, this.value, this.vecVal);
        return p;
    }

}
