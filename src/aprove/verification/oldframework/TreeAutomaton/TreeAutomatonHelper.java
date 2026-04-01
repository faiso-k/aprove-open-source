package aprove.verification.oldframework.TreeAutomaton;

import java.util.*;

/**
 * @author Marcel Klinzing
 */
public class TreeAutomatonHelper {
    public static <T> Set<Set<T>> powerSet(final Set<T> set) {
        final HashSet<Set<T>> powerSet = new LinkedHashSet<Set<T>>();
        powerSet.add(new HashSet<T>());

        for (final T t : set) {
            final ArrayList<Set<T>> listOfNewSubsets = new ArrayList<Set<T>>();
            for (final Set<T> s : powerSet) {
                final Set<T> s1 = new LinkedHashSet<T>(s);
                s1.add(t);
                listOfNewSubsets.add(s1);
            }
            powerSet.addAll(listOfNewSubsets);
        }
        return powerSet;
    }

    public static <T> Set<Set<T>> subSets(Set<Set<T>> setOfSets) {
        Set<Set<T>> setOfSubsets = new LinkedHashSet<Set<T>>();

        for (Set<T> set : setOfSets) {
            setOfSubsets.addAll(TreeAutomatonHelper.powerSet(set));
        }

        return setOfSubsets;
    }

    /**
     * Returns a map representing the epsilon transitions that are contained in
     * both parameters. This map may be modified.
     */
    public static <Z> Map<Z, Set<Z>> unionEpsTransitions(Map<Z, Set<Z>> epsTrans1, Map<Z, Set<Z>> epsTrans2) {
        final LinkedHashMap<Z, Set<Z>> unionedEpsTransitions = new LinkedHashMap<Z, Set<Z>>(epsTrans1);
        for (Map.Entry<Z, Set<Z>> entry : epsTrans2.entrySet()) {
            Z key = entry.getKey();
            Set<Z> knownValue = unionedEpsTransitions.get(key);
            if (knownValue != null) {
                Set<Z> newValue = new LinkedHashSet<Z>(knownValue);
                newValue.addAll(entry.getValue());
                unionedEpsTransitions.put(key, newValue);
            } else {
                unionedEpsTransitions.put(key, entry.getValue());
            }

        }

        return unionedEpsTransitions;
    }
}
