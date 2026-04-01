package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

/**
 * @author Tim Enger
 */

public class Combinations<T> {

    /**
     * Generates all possible combinations w.r.t a given List of possibilities
     * and length <br>
     * Example:<br>
     * list = {1,2,3}, length = 2 <br>
     * Combinations:<br>
     * {1,2}, {1,3}, {2,1}, {2,2}, {2,3}, {3,1}, {3,2}, {3,3}
     * @param <T>
     * @param list possible values
     * @param length determines the size of a combination
     * @return all possible combinations
     */
    public static <T> List<List<T>> createCombinations(List<T> list, int length) {
        ArrayList<List<T>> permutations = new ArrayList<List<T>>();
        ArrayList<T> permutation = new ArrayList<T>(length);
        for (int i = 0; i < length; i++) {
            permutation.add(null);
        }
        Combinations.computeCombinations(list, permutation, permutations, length, 0);
        return permutations;
    }

    private static <T> void computeCombinations(List<T> list,
        List<T> permutation,
        List<List<T>> permutations,
        int length,
        int pos) {

        if (pos == length) {
            permutations.add(new ArrayList<T>(permutation));
        } else {
            for (T element : list) {
                permutation.set(pos, element);
                Combinations.computeCombinations(list, permutation, permutations, length,
                    pos + 1);
            }
        }
    }

}
