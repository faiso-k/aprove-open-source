package aprove.verification.oldframework.Rewriting.SemanticLabelling;


import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Logic.*;

/**
 * A convenience class to iterate over all possible combinations of
 * values for a specified number of integers.
 */

public class VectorElementVectorIterator implements Iterator<int[][]>{

    private int numberOfVars;
    private int lengthOfVector;
    private int elements;
    private boolean first = true;
    private int[][] vectors;

    /**
     * Creates a new <code>ElementVectorIterator</code> instance.
     *
     * @param numberOfVars the length of the outer permutating vector
     * @param lengthOfInnerVector the length of the inner vectors
     * @param elements the number of element values to permutate over
     */
    public VectorElementVectorIterator(int numberOfVars, int lengthOfInnerVector, int elements) {
    this.numberOfVars = numberOfVars;
    this.lengthOfVector = lengthOfInnerVector;
    this.elements = elements;
    this.vectors = new int[numberOfVars][lengthOfInnerVector];

    }

    /**
     * Checks if another possible combination of element values is
     * available.
     *
     * @return <code>true</code> if another combination is available,
     * <code>false</code> otherwise
     */
    @Override
    public boolean hasNext() {
        if (this.first) {
            return true;
        }
        for (int i = 0; i < this.numberOfVars; i++) {
            for(int j=0; j<this.lengthOfVector; j++) {
                if (this.vectors[i][j] < this.elements - 1) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Gets the next array of vectors of integers with another combination of
     * numbers.
     *
     * @return an <code>Array</code> of <code>int</code>s, casted as
     * an <code>Object</code>.
     */
    @Override
    public int[][] next() {
        int plusOne;
        if (this.first) {
            this.first = false;
            for (int i = 0; i<this.numberOfVars; i++) {
                for(int j=0; j<this.lengthOfVector; j++) {
                    this.vectors[i][j] = 0;
                }
            }
            return this.vectors;
        }
        for(int i= (this.numberOfVars-1); i>=0; i--) {
            for(int j= (this.lengthOfVector-1); j>=0; j--) {
                if(this.vectors[i][j] <= (this.elements-2)) {
                    plusOne = (this.vectors[i][j] +1);
                    this.vectors[i][j] = plusOne;
                    return this.vectors;
                }
                else {
                    this.vectors[i][j] = 0;
                }
            }
        }
        return null;
    }

    /**
     * This method is not implemented
     *
     */
    @Override
    public void remove() {
    }

    /**
     *  lexicographic comparison with the leftmost vector
     *  as the most significant, and inside a vector the leftmost
     *  position is the most significant as well.
     * @param small
     * @return the next bigger element or null (if there is no bigger element)
     */
    public static ArrayList<int[]> getNextBiggerElementLexicographic(ArrayList<int[]> small, int carrierSize) {
        ArrayList<int[]> returnValue = new ArrayList<int[]>();
        for(int i=0; i<small.size(); i++) {
            int arraySize = small.get(i).length;
            Set<Integer> s = new HashSet<Integer>();
            if(Globals.useAssertions) {
                s.add(arraySize);
                assert(s.size() == 1);
            }
            int[] dummy = new int[arraySize];
            System.arraycopy(small.get(i), 0, dummy, 0, arraySize);
            returnValue.add(dummy);

        }
        for(int i= (returnValue.size() -1); i>=0; i--) {
            int[] actVector = returnValue.get(i);
            for(int j=(actVector.length -1); j>=0; j--) {
                int actValue = actVector[j];
                if(actValue < (carrierSize -1)) {
                    actVector[j] = ++actValue;
                    return returnValue;
                }
                else {
                    actVector[j] = 0;
                }
            }
        }
        return null;
    }

    /**
     * Lexicographic comparison of two "vectors"
     * with the leftmost position (0 index of array)
     * as the most siginificant. Both elements must have
     * equal length!<br>
     * E.g. [1,0] is bigger than [0,1] <br>
     *      [0,1,0] is incomparable to [0,1]
     *
     * @param thiss the element which is supposed to be bigger
     * @param other the element which is supposed to be smaller
     * @return YES iff thiss and other are comparable and thiss is strictly bigger<br>
     *         MAYBE iff they are equal, NO otherwise
     */
    public static YNM isBigger(int[] thiss, int[] other) {
        if(Globals.useAssertions) {
            assert(thiss.length == other.length) : "VectorElementVectorIterator: Comparison of two arrays with different length is not defined!";
        }
        for(int i=0; i<thiss.length; i++) {
            if(thiss[i] == other[i]) {
                continue;
            }
            else {
                if(thiss[i] > other[i]) {
                    return YNM.YES;
                }
                else {
                    return YNM.NO;
                }
            }
        }
        return YNM.MAYBE;
    }

}
