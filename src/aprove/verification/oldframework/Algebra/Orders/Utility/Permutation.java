package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;


/** Encapsulation of a permutation of {0, 1, ..., n-1}.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class Permutation {
    private int[] perm;

    /* constructors */

    //  Default constructor should only be used publicly by XML serialization.
    public Permutation() {

    }

    public static boolean isPermutation(int[] perm) {
        int n = perm.length;
        if (n == 1 && perm[0] < 0) {
            return true;
        }
        boolean[] used = new boolean[n];
        for (int i = 0; i < n; i++) {
            used[perm[i]] = true;
        }
        for (int i = 0; i < n; i++) {
            if (!used[i]) {
                return false;
            }
        }
        return true;
    }

    private Permutation(int[] perm) {
        assert(Permutation.isPermutation(perm));
    this.perm = perm;
    }

    /** Creates a new instance of <code>Permutation</code>.
     * @param perm   the permutation that should be encapsulated, perm must not be modified after calling.
     */
    static public Permutation create(int[] perm) {
    return new Permutation(perm);
    }

    /** Creates a new instance of <code>Permutation</code>.
     * @param perm the permutation that should be encapsulated, perm may be modified after calling.
     */
    static public Permutation createSafe(int[] perm) {
        int n = perm.length;
        int[] copy = new int[n];
        System.arraycopy(perm, 0, copy, 0, n);
        return new Permutation(copy);
    }

    static public Permutation createLeftToRight(int n) {
        int[] lr = new int[n];
        for (int i = 0; i < n; i++) {
            lr[i] = i;
        }
        return new Permutation(lr);
    }

    static public Permutation createRightToLeft(int n) {
        int[] rl = new int[n];
        for (int i = 0; i < n; i++) {
            rl[i] = n-i-1;
        }
        return new Permutation(rl);
    }

    /** Return the number at position <code>i</code> if 0 <= <code>i</code>
     *  <= n-1, <code>-1</code> otherwise.
     */
    public int get(int i) {
    if (i<0 || i>=this.perm.length) {
        return -1;
    }
    else {
        return this.perm[i];
    }
    }

    /** Returns <code>n</code>.
     */
    public int size() {
    return this.perm.length;
    }

    /** Returns a string representation of the object where the values are
     * transformed to {1,...,n}.
     */
    @Override
    public String toString() {
    StringBuilder res = new StringBuilder("[");

        int n = this.perm.length;
    for (int i=0; i<n; i++) {
        res.append(this.perm[i]+1);
        if(i < n-1) {
        res.append(",");
        }
    }

    res.append("]");

    return res.toString();
    }

    /** Returns <code>true</code> if the two objects represent the same
     * permutation, <code>false</code> otherwise.
     */
    @Override
    public boolean equals(Object o) {
        if (o == null) {
            return false;
        }
        Permutation other;
    try {
        other = (Permutation)o;
            return Arrays.equals(this.perm, other.perm);
        }
    catch(ClassCastException e) {
        return false;
    }

    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(this.perm);
    }

}
