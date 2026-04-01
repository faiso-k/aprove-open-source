package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

/** This class is a permutation generator.
 * <p>
 * The permutations are generated
 * using Dershowitz's method, meaning that a permutation only differs
 * by the previous permutation by a single interchange of two adjacent
 * elements. In many problem domains this allows a efficient dynamic
 * update of a permutation function.
 * <p>
 * Dershowitz, Nachum. "A simplified loop-free algorithm for generating permutations" BIT-15 1975 158-164
 *
 * @author Peter Unold, http://www.daimi.au.dk/~pjunold/alg/dershowitz.html,
 *         modified for AProVE by Stephan Falke
 * @version $Id$
 */

public class PermutationGenerator implements Iterable<Permutation> {

    private int n;

    private final static int STORE_LIMIT = 10;

    private final static PermutationGenerator[] somePerms;
    static {
        somePerms = new PermutationGenerator[PermutationGenerator.STORE_LIMIT];
        for (int i=0; i<PermutationGenerator.STORE_LIMIT; i++) {
            PermutationGenerator.somePerms[i] = new PermutationGenerator(i);
        }
    }

    public static PermutationGenerator create(int n) {
        if (n < PermutationGenerator.STORE_LIMIT) {
            return PermutationGenerator.somePerms[n];
        } else {
            return new PermutationGenerator(n);
        }
    }

    private PermutationGenerator(int n) {
        this.n = n;
    }

    /** Creates a new instance of <code>PermutationGenerator</code>.
     * @param n   specifies the size of the set whose permutations should
     *            be generated
     */
    @Override
    public Iterator<Permutation> iterator() {
        return new PermutationIterator(this.n);
    }



    private class PermutationIterator implements Iterator<Permutation> {
        private int[] permutation;
        private int[] location;
        private int[] m_t; // linked list
        private int[] direction;
        private boolean more;
        private int size;

        /* constructors */

        private PermutationIterator(int size) {
            this.size = size;
            this.more = size>0;
            this.permutation = new int[size];
            this.location = new int[size];
            this.m_t = new int[size+1];
            this.direction = new int[size];

            /* initialize the identity permutation */
            for (int i=0; i<size; i++) {
                this.permutation[i] = i;
                this.location[i] = i;
                this.direction[i] = -1;
            }

            for(int j=1; j<=size; j++) {
                this.m_t[j] = j-1;
            }
        }


        /* generates the next permutation. If the function returns n, then the
         * elements at position n and n+1 in the previous permutation were
         * interchanged to get the new permutation.
         */
        private int calcNextPermutation() {
            int cur, neig, curpos, neigpos, neigpos2;

            // 3
            if(this.m_t[this.size]<1) {
                return -1;
            }

            // 4
            cur = this.m_t[this.size];
            curpos = this.location[cur];
            neigpos = curpos + this.direction[cur];

            neig = this.permutation[neigpos];

            // 5
            this.location[cur] = neigpos;
            this.location[neig] = curpos;
            this.permutation[curpos] = neig;
            this.permutation[neigpos] = cur;

            // 6
            this.m_t[this.size] = this.size-1;

            // 7
            neigpos2 = neigpos + this.direction[cur];

            if (neigpos2<0 || neigpos2>=this.size || cur<this.permutation[neigpos2]) {
                this.direction[cur] = -this.direction[cur];
                this.m_t[cur+1] = this.m_t[cur];
                this.m_t[cur] = cur-1;
            }

            return curpos<neigpos ? curpos : neigpos;
        }


        /** Returns the next permutation.
         */
        @Override
        public Permutation next() {
            Permutation ret = Permutation.createSafe(this.permutation);
            if (this.calcNextPermutation() == -1) {
                this.more = false;
            }

            return ret;
        }

        /* Returns <code>true</code> if there are more permutations,
         * <code>false</code> otherwise.
         */
        @Override
        public boolean hasNext() {
            return this.more;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

}
