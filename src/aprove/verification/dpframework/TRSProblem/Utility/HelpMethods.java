package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

/**
 * this class simply provides useful Help-Methods of any kind
 *      and may be extended by anyone
 *
 * @author Sebastian Weise
 */

public class HelpMethods {

    /**
     * this Sub-Class provides Help-Methods operating on Sets of the Type "T"
     */
    public static class MethodsForSets<T> {

        /**
         * this method returns the Set of all non-empty Subsets of a Set;
         * if "set == null" then "Null" is returned;
         * if "set.isEmpty() == true" then the empty Set of Sets is returned
         *
         * no Side-Effects on Parameter-Set "set" !
         */
        public Set<Set<T>> getAllNonemptySubsets(final Set<T> set) {

            if (set == null) {
                return null;
            }

            final Set<Set<T>> result = new LinkedHashSet<Set<T>>();

            if (set.isEmpty()) {
                return result;
            }

            // set is non-empty

            final T element = set.iterator().next();

            final Set<T> setContainingExactlyElement = new LinkedHashSet<T>();
            setContainingExactlyElement.add(element);
            result.add(setContainingExactlyElement);

            final Set<T> restSet = new LinkedHashSet<T>(set);
            restSet.remove(element);

            final Set<Set<T>> allNonemptySubsetsOfRestSet =
                this.getAllNonemptySubsets(restSet);

            result.addAll(allNonemptySubsetsOfRestSet);

            for (final Set<T> actSubset : allNonemptySubsetsOfRestSet) {
                final Set<T> newSubsetWithElement =
                    new LinkedHashSet<T>(actSubset);
                newSubsetWithElement.add(element);
                result.add(newSubsetWithElement);
            }

            return result;
        }

        /**
         * this method merges all non-disjunct Sets in a Set of Sets;
         * corresponding Side-Effects on the Parameter!
         * after executing this method all Sets in "setOfSets" will
         *      be pairwise disjunct to each other
         */
        public void merge(final Set<Set<T>> setOfSets) {
            if (!setOfSets.isEmpty()) {
                final Set<T> removedSet = setOfSets.iterator().next();
                setOfSets.remove(removedSet);
                this.merge(setOfSets);
                for (final Set<T> actSet : setOfSets) {
                    final Set<T> intersection =
                        new LinkedHashSet<T>(removedSet);
                    intersection.retainAll(actSet);
                    if (!intersection.isEmpty()) {
                        removedSet.addAll(actSet);
                        setOfSets.remove(actSet);
                    }
                }
                setOfSets.add(removedSet);
            }
        }
    }
}
