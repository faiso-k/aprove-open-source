package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

/**
 * A convenience class to iterate over all possible combinations of
 * values for a specified number of integers.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version 1.0
 */
public class ElementVectorIterator implements Iterator<int[]> {

    private int length;
    private int elements;
    private boolean first = true;
    private int[] vector;

    /**
     * Creates a new <code>ElementVectorIterator</code> instance.
     *
     * @param length the length of the permutating vector
     * @param elements the number of element value to permutate over
     */
    public ElementVectorIterator(int length, int elements) {

    this.length = length;
    this.elements = elements;
    this.vector = new int[length];

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
    for (int i = 0; i < this.length; i++) {
        if (this.vector[i] < this.elements - 1) {
        return true;
        }
    }

    return false;

    }

    /**
     * Gets the next array of integers with another combination of
     * numbers.
     *
     * @return an <code>Array</code> of <code>int</code>s, casted as
     * an <code>Object</code>.
     */
    @Override
    public int[] next() {

    if (this.first) {
        this.first = false;
        for (int i = 0; i < this.length; i++) {
        this.vector[i] = 0;
        }
        return this.vector;

    }

    for (int i = this.length - 1; i >= 0; i--) {
        if (this.vector[i] <= this.elements - 2) {
        this.vector[i]++;
        return this.vector;
        }
        if (this.vector[i] == this.elements - 1) {
        this.vector[i] = 0;
        }

    }

    return this.vector;

    }

    /**
     * This method is not implemented
     *
     */
    @Override
    public void remove() {
    }

}
