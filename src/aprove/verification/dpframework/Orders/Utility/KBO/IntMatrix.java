package aprove.verification.dpframework.Orders.Utility.KBO;

import java.math.*;
import java.util.*;

import aprove.*;

/**
 * This class represents a simple integer matrix as a vector of
 * column vectors.
 * @author Achim Luecking, R. Thiemann
 * @version 2003/05/25
 */
public final class IntMatrix {

    private static final BigInteger ZERO = BigInteger.ZERO;

    // List of column vectors
    private final List<List<BigInteger>> column;

    // number of rows
    private final int rows;

    private int hashCode = 0;
    private boolean hashValid = false;

    /**
     * Constructor. Do not modify the columns-set after calling this constructor!
     */
    public IntMatrix(List<List<BigInteger>> columns, int rowSize) {
        this.column = columns;
        this.rows = rowSize;
        if (Globals.useAssertions) {
            for (List<BigInteger> col : columns) {
                assert(this.rows == col.size());
            }
        }
    }

    /**
     * Multiplies another matrix to this matrix (this*other).
     * @param other the matrix, which should be multiplied with this matrix
     * @return the result matrix
     */
    public IntMatrix multiply(IntMatrix other) {
        ArrayList<List<BigInteger>> columns = new ArrayList<List<BigInteger>>(other.column.size());
        for (List<BigInteger> element : other.column) {
            List<BigInteger> add = this.multiply(element);
            columns.add(add);
        }
        return new IntMatrix(columns, this.rows);
    }

    /**
     * Multiplies two vectors: a row vector a and a column vector b (a*b).
     * This is equivalent to the multiplication of a (1xn) matrix with a
     * (nx1) matrix.
     * @param a the row vector
     * @param b the column vector
     * @return the int result of this multiplication
     */
    private BigInteger multiplyVectors(List<BigInteger> a, List<BigInteger> b){
        if (Globals.useAssertions) {
            assert(a.size() == b.size());
        }
        BigInteger result = IntMatrix.ZERO;
        for (int i=0; i<a.size(); i++){
            BigInteger x = a.get(i);
            BigInteger y = b.get(i);
            result = result.add(x.multiply(y));
        }
        return result;
    }

    /**
     * Multiplies this matrix to a row vector (v*A).
     * @param v the row vector
     * @return the resulting vector of the multiplication
     */
    public List<BigInteger> multiplyRow(List<BigInteger> v) {
        List<BigInteger> neu = new ArrayList<BigInteger>(this.column.size());
        for (List<BigInteger> element : this.column) {
            BigInteger i = this.multiplyVectors(element,v);
            neu.add(i);
        }
        return neu;
    }

    /**
     * Multiplies a column vector to this matrix (A*v).
     * @param v the column vector
     * @return the resulting vector of the multiplication
     */
    public List<BigInteger> multiply(List<BigInteger> v) {
        if (Globals.useAssertions) {
            assert(v.size()==this.column.size());
        }
        List<BigInteger> neu = new ArrayList<BigInteger>(this.rows);
        for (int j=0; j<this.rows; j++) {
            BigInteger added = IntMatrix.ZERO;
            for (int i=0; i<v.size(); i++){
                BigInteger x = v.get(i);
                List<BigInteger> col = this.column.get(i);
                BigInteger y = col.get(j);
                added = added.add(x.multiply(y));
            }
            neu.add(added);
        }
        return neu;
    }

    /**
     * Returns the row dimension of this matrix.
     * @return the row dimension
     */
    public int rows(){
        return this.rows;
    }

    /**
     * Returns the vector of column vectors.
     * @return the vector of column vectors
     */
    public List<List<BigInteger>> toVectors(){
        return this.column;
    }

    /**
     * Returns a unsorted set of the column vectors.
     * @return a unsorted set of the column vectors
     */
    public Set<List<BigInteger>> toSet(){
        return new LinkedHashSet<List<BigInteger>>(this.column);
    }

    /**
     * Returns, whether another object o equals this matrix.
     */
    @Override
    public boolean equals(Object o){
        IntMatrix other = (IntMatrix) o;
        return this.column.equals(other.column);
    }

    /**
     * Returns a string representation of this matrix.
     */
    @Override
    public String toString(){
        return this.column.toString();
    }

    /**
     * Returns the hash code of this matrix.
     */
    @Override
    public int hashCode(){
        if (!this.hashValid) {
            this.hashCode = this.column.hashCode();
            this.hashValid = true;
        }
        return this.hashCode;
    }

}
