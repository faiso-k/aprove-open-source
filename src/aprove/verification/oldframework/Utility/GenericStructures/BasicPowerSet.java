package aprove.verification.oldframework.Utility.GenericStructures;

import static aprove.verification.oldframework.Logic.YNM.*;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Comment: a class that gives all possible subsets of {0,1,...,power-1} in
 *                 a breadth first way, that means, first is the emptyset returned, then
 *                 all singleton sets, ...
 *          one can further restrict the size of the subsets.
 * @author thiemann
 */
public class BasicPowerSet implements Iterable<boolean[]> {


    private final int startSearchSize; // size to search for at the beginning
    private final int endSearchSize; // size to search for at the end
    private final int searchPower; // power of the maybe-part
    private final YNM[] pattern; // the pattern
    private final boolean reverse;
    private final int levelIncDec;

    private static final int preComputedNr = 10;
    private static final YNM[][] somePatterns;
    static {
        somePatterns = new YNM[BasicPowerSet.preComputedNr][];
        for (int i=0; i<BasicPowerSet.preComputedNr; i++) {
            BasicPowerSet.somePatterns[i] = BasicPowerSet.computeMaybePattern(i);
        }
    }



    public static YNM[] computeMaybePattern(int arity) {
        YNM[] maybePattern = new YNM[arity];
        for (int i=0; i<arity; i++) {
            maybePattern[i] = YNM.MAYBE;
        }
        return maybePattern;
    }

    public static YNM[] getMaybePattern(int arity) {
        if (arity < BasicPowerSet.preComputedNr) {
            return BasicPowerSet.somePatterns[arity];
        } else {
            return BasicPowerSet.computeMaybePattern(arity);
        }
    }

    /**
     * @param power - the number of elements of the base set
     */
    public BasicPowerSet (int power) {
        this(BasicPowerSet.getMaybePattern(power),power, false);
    }



    /**
     * @param power - the number of elements of the base set
     * @param maxSize - the maximal Size of a returned subset
     * @param reversed - reverses the order, i.e. large sets are returned first
     */
    public BasicPowerSet (int power, int maxSize, boolean reversed) {
        this(BasicPowerSet.getMaybePattern(power), maxSize, reversed);
    }

    /**
     * @param power - the number of elements of the base set
     * @param maxSize - the maximal Size of a returned subset
     */
    public BasicPowerSet (int power, int maxSize) {
        this(power, maxSize, false);
    }


    public BasicPowerSet (int power, int maxSize, YNM[] pattern, boolean reverse) {
        this(pattern == null ? BasicPowerSet.getMaybePattern(power) : pattern, maxSize, reverse);
    }

    public BasicPowerSet(YNM[] pattern, int maxSize) {
        this(pattern, maxSize, false);
    }

    /**
     * @param pattern - a non-null pattern of YNM values, only maybe values will be chosen freely!
     * @param maxSize - limit size of subsets to this integer
     * @param reverse - reverses the order, i.e. large sets are returned first
     */
    public BasicPowerSet(YNM[] pattern, int maxSize, boolean reverse) {
        if (Globals.useAssertions) {
            assert(pattern != null);
            for (YNM ynm : pattern) {
                assert(ynm != null);
            }
        }
        int yesCount = 0;
        int maybeCount = 0;
        int n = pattern.length;
        for (int i=0; i<n; i++) {
            YNM status = pattern[i];
            if (status == YES) {
                yesCount++;
            } else if (status == MAYBE) {
                maybeCount++;
            }
        }
        int noCount = n-yesCount-maybeCount;
        int maxPower = pattern.length - noCount;
        maxSize = maxSize > maxPower ? maxPower : maxSize;
        this.reverse = reverse;
        int nrUnknowns = maxSize - yesCount;
        if (nrUnknowns < 0) {
            nrUnknowns = -1;
        }
        if (this.reverse) {
            this.levelIncDec = -1;
            this.startSearchSize = nrUnknowns+1;
            this.endSearchSize = 0;
        } else {
            this.levelIncDec = 1;
            this.startSearchSize = -1;
            this.endSearchSize = nrUnknowns;
        }
        this.searchPower = maybeCount;
        this.pattern = pattern;
    }

    @Override
    public Iterator<boolean[]> iterator() {
        return new BoundedPowerSetIterator();
    }


    private class BoundedPowerSetIterator implements Iterator<boolean[]> {

        private int searchSize; // current setsize
        private int vec[]; // positions of the elements
        private boolean notYetDone; // is curIntVec a valid value

        private BoundedPowerSetIterator() {
            this.searchSize = BasicPowerSet.this.startSearchSize;
            this.notYetDone = true;
            this.nextLevel();
        }

        /**
         * @return gives the next boolean array where res[i] is true iff i is in the set
         */
        @Override
        public boolean[] next() {
            if (this.notYetDone) {
                int n = BasicPowerSet.this.pattern.length;
                boolean[] res = new boolean[n];
                int[] vec = this.vec;
                int m = vec.length;
                int nextMaybe = m == 0 ? -1 : vec[0];
                int positionCount = 1;
                int maybeCount = -1;
                for (int i=0; i<n; i++) {
                    YNM status = BasicPowerSet.this.pattern[i];
                    if (status == YES) {
                        res[i] = true;
                    } else if (status == NO) {
                        res[i] = false;
                    } else {
                        maybeCount++;
                        if (maybeCount == nextMaybe) {
                            res[i] = true;
                            if (positionCount < m) {
                                // we have new maybeValue
                                nextMaybe = vec[positionCount];
                                positionCount++;
                            } else {
                                nextMaybe = -1;
                            }
                        } else {
                            res[i] = false;
                        }
                    }
                }
                this.calcNext();
                return res;
            } else {
                throw new NoSuchElementException();
            }
        }


        /**
         * @return boolean gives the result if there is a next element or not
         */
        @Override
        public boolean hasNext() {
            return this.notYetDone;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }


//      calculates the next vector
        private void calcNext() {
            // first try to detect shift-position
            int i=0;
            while (i < this.searchSize && this.vec[i] == i) {
                //      walk to shiftable element
                i += 1;
            }

            if (i == this.searchSize) {
                // nothing to shift, so take next level (size)
                this.nextLevel();
                return;
            }

            // put element i one step right
            this.vec[i] -= 1;

            // and update the remaining elements left of the shift element
            int pos = this.vec[i];
            while (i > 0) {
                pos -= 1;
                i -= 1;
                this.vec[i] = pos;
            }
        }


        private void nextLevel() {
            if (this.searchSize == BasicPowerSet.this.endSearchSize) {
                this.notYetDone = false;
            } else {
                this.searchSize += BasicPowerSet.this.levelIncDec;
                this.vec = new int[this.searchSize];
                int i = 0;
                int base = BasicPowerSet.this.searchPower-this.searchSize;
                while (i < this.searchSize) {
                    this.vec[i] = i+base;
                    i++;
                }
            }
        }
    }
}
