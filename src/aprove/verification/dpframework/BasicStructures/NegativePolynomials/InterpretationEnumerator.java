/**
 * Created on 17.03.2005
 *
 * @author thiemann
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class InterpretationEnumerator implements Iterable<int[]> {

    private final int arity;
    private final int range;
    private final boolean negative;
    private final int maxSize;
    private final boolean reverse;
    private final YNM[] pattern;


    public InterpretationEnumerator(int arity, int range, boolean reverse) {
        this(BasicPowerSet.getMaybePattern(arity), range, arity, reverse);
    }

    public InterpretationEnumerator(int arity, int range, int maxSize, YNM[] pattern, boolean reverse) {
        this(pattern == null ? BasicPowerSet.getMaybePattern(arity) : pattern, range, maxSize, reverse);
    }


    /**
     * enumerates possible interpretations for a function symbol of
     * given arity where coefficients are in the given range
     * (the constant is from -range to +range).
     * The maxSize restricts the number of (non-constant) coefficients
     * that are different from zero.
     * @param pattern - the pattern for creation (non-null)
     * @param range
     * @param maxSize
     */
    public InterpretationEnumerator(YNM[] pattern, int range, int maxSize, boolean reverse) {
        if (range == 0 || pattern == null) {
            throw new RuntimeException("Bad values for Interpretation Enumerator");
        }
        this.negative = range < 0;
        this.range = this.negative ? -range : range;
        this.maxSize = maxSize;
        this.pattern = pattern;
        this.arity = pattern.length;
        this.reverse = reverse;
    }

    @Override
    public Iterator<int[]> iterator() {
        return new RangeIterator();
    }


    private class RangeIterator implements Iterator<int[]> {

        private final Iterator<boolean[]> positionSetIterator; // gives the different positions
        private int constant; // the value of the current constant
        private int[] rangeVec; // the values of the coefficients on the positionsVec
        private int[] positionVec; // the positions of the non-zero coefficients
        private boolean notYetDone;
        private int currentSize; // the current nr of non-zero coefficients (=size rangeVec,positionVec)
        private int minConstant; // the minimal constant for the current size

        private RangeIterator() {
            this.positionSetIterator = new BasicPowerSet(InterpretationEnumerator.this.pattern, InterpretationEnumerator.this.maxSize, InterpretationEnumerator.this.reverse).iterator();
            this.notYetDone = true;
            this.nextPosition();
        }

        @Override
        public int[] next() {
            if (this.notYetDone) {
                // prepare final result
                int[] res = new int[InterpretationEnumerator.this.arity+1];
                res[0] = this.constant;

                int posCount = 0;
                int nextPos = posCount < this.positionVec.length ? this.positionVec[posCount] : -1;
                for (int i=0; i < InterpretationEnumerator.this.arity; ) {
                    if (i == nextPos) {
                        i++;
                        res[i] = this.rangeVec[posCount];
                        posCount++;
                        nextPos = posCount < this.positionVec.length ? this.positionVec[posCount] : -1;
                    } else {
                        i++;
                        res[i] = 0;
                    }
                }

                // and calculate the next one
                this.calcNext();

                return res;
            } else {
                throw new NoSuchElementException();
            }
        }


        private void calcNext() {
            // first enumerate different constants
            if (this.constant < InterpretationEnumerator.this.range) {
                this.constant++;
                return;
            }

            // next try to find a shift position
            // first try to detect shift-position
            int i=0;
            while (i < this.currentSize && this.rangeVec[i] == InterpretationEnumerator.this.range) {
                //      walk to shiftable element
                i ++;
            }

            // if there is nothing to shift, take next position
            if (i == this.currentSize) {
                this.nextPosition();
                return;
            }

            // reset constant
            this.constant = this.minConstant;

            // increase element i by 1
            this.rangeVec[i] ++;

            // and update the remaining elements left of the increased element
            while (i > 0) {
                i --;
                this.rangeVec[i] = 1;
            }

        }

        private void nextPosition() {
            if (this.positionSetIterator.hasNext()) {
                boolean[] boolPositionVec = this.positionSetIterator.next();
                int n = 0;
                for (int i=0; i < InterpretationEnumerator.this.arity; i++) {
                    if (boolPositionVec[i]) {
                        n++;
                    }
                }
                this.positionVec = new int[n];
                int j = 0;
                for (int i=0; i < n; i++) {
                    while (!boolPositionVec[j]) {
                        j++;
                    }
                    this.positionVec[i] = j;
                    j++;
                }
                this.currentSize = n;
                this.minConstant = (InterpretationEnumerator.this.negative && n != 0) ? -InterpretationEnumerator.this.range : 0;
                this.constant = this.minConstant;
                this.rangeVec = new int[n];
                for (int i=0; i<n; i++) {
                    this.rangeVec[i] = 1;
                }
            } else {
                this.notYetDone = false;
            }
        }

        @Override
        public boolean hasNext() {
            return this.notYetDone;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

}
