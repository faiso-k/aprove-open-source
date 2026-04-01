package aprove.verification.dpframework.TRSProblem.Processors;

public class ArrayPermutator {

    private int length;
    private int maxElement;
    private boolean first = true;
    private int[] array;

    /**
     * Creates a new <code>ArrayPermutator</code> instance.
     *
     * @param length the length of the permutating vector
     * @param elements the number of element value to permutate over
     */
    public ArrayPermutator(int length, int elements) {

    this.length = length;
    this.maxElement = elements;
    this.array = new int[length];

    }

    /**
     * Checks if another possible combination of element values is
     * available.
     *
     * @return <code>true</code> if another combination is available,
     * <code>false</code> otherwise
     */
    public boolean hasNext() {

    if (this.first) {
        return true;
    }
    for (int i = 0; i < this.length; i++) {
        if (this.array[i] < this.maxElement - 1) {
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
    public int[] next() {

    if (this.first) {
        this.first = false;
        for (int i = 0; i < this.length; i++) {
            this.array[i] = 0;
        }
        return this.array;
    }

    for (int i = this.length - 1; i >= 0; i--) {
        if (this.array[i] <= this.maxElement - 2) {
            this.array[i]++;
            return this.array;
        }
        if (this.array[i] == this.maxElement - 1) {
        this.array[i] = 0;
        }
    }
    return this.array;
    }

}
