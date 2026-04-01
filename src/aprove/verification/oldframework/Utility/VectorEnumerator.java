/**
 * Created on 31.07.2008
 *
 * @author thiemann
 */
package aprove.verification.oldframework.Utility;

import java.util.*;

public class VectorEnumerator implements Iterable<int[]> {

    private final int arity;
    private final int range;


    /**
     * enumerates all elements in {0,1,..,range}^arity.
     * Note that the returned int[] may not be modified!
     * @param arity a natural number
     * @param range a natural number
     */
    public VectorEnumerator(int arity, int range) {
        this.arity = arity;
        this.range = range;
        assert(arity >= 0 && range >= 0);
    }


    @Override
    public Iterator<int[]> iterator() {
        return new VectorIterator();
    }


    private class VectorIterator implements Iterator<int[]> {

        private final int[] currVec; // the current vector
        private boolean nextValid;
        private boolean notYetDone;

        private VectorIterator() {
            this.currVec = new int[VectorEnumerator.this.arity];
            for (int i = 0; i < VectorEnumerator.this.arity; i++) {
                this.currVec[i] = 0;
            }
            this.notYetDone = true;
            this.nextValid = true;
        }

        @Override
        public int[] next() {
            if (this.hasNext()) {
                this.nextValid = false;
                return this.currVec;
            } else {
                throw new NoSuchElementException();
            }
        }


        private void calcNext() {
            // first try to detect shift-position
            int i=0;
            while (i < VectorEnumerator.this.arity && this.currVec[i] == VectorEnumerator.this.range) {
                //      walk to shiftable element
                i ++;
            }

            // if there is nothing to shift, we are done
            if (i == VectorEnumerator.this.arity) {
                this.notYetDone = false;
            } else {

                // increase element i by 1
                this.currVec[i] ++;

                // and update the remaining elements left of the increased element
                while (i > 0) {
                    i --;
                    this.currVec[i] = 0;
                }
            }

            this.nextValid = true;
        }

        @Override
        public boolean hasNext() {
            if (!this.nextValid) {
                this.calcNext();
            }
            return this.notYetDone;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

}
