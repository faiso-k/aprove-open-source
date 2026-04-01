package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

/** This class is a generator for sequences.
 * <p>
 * The sequences of length m of elements from {0, 1, ..., n-1} are generated
 * beginning with [0, 0, ..., 0], [0, 0, ..., 1], ... and ending with
 * ..., [n-1, n-1, ..., n-2], [n-1, n-1, ..., n-1].
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class SequenceGenerator implements Iterable<Sequence>
{

    private final int size;
    private final int n;


    /** Creates a new instance of <code>SequenceGenerator</code>.
     * @param size   specifies the length of the sequences
     * @param n      entries of the sequences will be among {0, 1, ..., n-1}
     */
    public static SequenceGenerator create(int size, int n) {
        return new SequenceGenerator(size, n);
    }

    private SequenceGenerator(int size, int n) {
        this.size = size;
        this.n = n;
    }

    @Override
    public Iterator<Sequence> iterator() {
        return new SequenceIterator();
    }



    private class SequenceIterator implements Iterator<Sequence> {

        private int[] next;
        private boolean hasNext;

        /* constructors */

        private SequenceIterator() {
            this.hasNext = SequenceGenerator.this.size>0 && SequenceGenerator.this.n>0;
            this.next = new int[SequenceGenerator.this.size];

            /* initialize the sequence consisting of 0's */
            for(int i=0; i<SequenceGenerator.this.size; i++) {
                this.next[i] = 0;
            }
        }


        /* generates the next sequence */
        private void calcNextSequence() {
            int pos;

            /* increment the last element in the sequence by 1 */
            pos = SequenceGenerator.this.size-1;
            this.next[pos]++;
            /* take care of overflows */
            while(this.next[pos]==SequenceGenerator.this.n) {
                /* overflow at position pos */
                this.next[pos] = 0;
                /* decrement pos by 1 (i.e., move one position to the right) and
                 * increment the element at this (new) position by 1
                 * Cool! C syntax really is unintelligible!
                 */
                this.next[--pos]++;
            }
        }


        /** Returns the next sequence.
         */
        @Override
        public Sequence next() {
            if (this.hasNext) {
                if(this.wasLastSequence()) {
                    this.hasNext = false;
                }
                Sequence ret = Sequence.create(this.next);
                if(this.hasNext) {
                    this.calcNextSequence();
                }

                return ret;
            } else {
                throw new NoSuchElementException();
            }
        }

        private boolean wasLastSequence() {
            for(int i=SequenceGenerator.this.size-1; i>=0; i--) {
                if(this.next[i]!=SequenceGenerator.this.n-1) {
                    return false;
                }
            }
            return true;
        }

        /* Returns <code>true</code> if there are more sequences,
         * <code>false</code> otherwise.
         */
        @Override
        public boolean hasNext() {
            return this.hasNext;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

}
