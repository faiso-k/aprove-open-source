package aprove.verification.oldframework.Bytecode.Intersector;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Convenience class holding the reference partitions for the intersector.
 *
 * @author Marc Brockschmidt
 */
public final class IntersectorRefPartition {
    /**
     * The actual partition, mapping each state/ref pair to its eqivalence
     * class.
     */
    private ImmutableMap<StateAndRef, ImmutableSet<StateAndRef>> partition;

    /** Mapping to one fresh name for each equivalence class */
    private ImmutableMap<ImmutableSet<StateAndRef>, AbstractVariableReference> freshNames;

    /**
     * @param res the partition
     */
    private IntersectorRefPartition(final ImmutableMap<StateAndRef, ImmutableSet<StateAndRef>> res) {
        this.partition = res;
        final LinkedHashMap<ImmutableSet<StateAndRef>, AbstractVariableReference> freshNameMap = new LinkedHashMap<>();
        for (final ImmutableSet<StateAndRef> eqClass : res.values()) {
            final Iterator<StateAndRef> it = eqClass.iterator();
            AbstractVariableReference oldRefName = it.next().y;
            boolean allRefsEqual = true;
            while (it.hasNext()) {
                final AbstractVariableReference otherOldRef = it.next().y;
                allRefsEqual &= oldRefName.equals(otherOldRef);
                if (otherOldRef.pointsToConstant()) {
                    oldRefName = otherOldRef;
                } else if (otherOldRef.pointsToArray()) {
                    oldRefName = otherOldRef;
                }
            }

            final AbstractVariableReference newRef;
            if (allRefsEqual) {
                newRef = oldRefName;
            } else {
                newRef = AbstractVariableReference.create(oldRefName);
            }
            freshNameMap.put(eqClass, newRef);
        }
        this.freshNames = ImmutableCreator.create(freshNameMap);

        for (final Entry<StateAndRef, ImmutableSet<StateAndRef>> entry : res.entrySet()) {
            final AbstractVariableReference ref = entry.getKey().y;
            if (!ref.pointsToArray()) {
                continue;
            }
            if (Globals.useAssertions) {
                final AbstractVariableReference newRef = this.freshNames.get(entry.getValue());
                assert (newRef.pointsToArray() || newRef.isNULLRef());
            }
        }
    }

    /**
     * @param s1 some state
     * @param s2 some other state
     * @return reference partition in which two references (s,r), (s',r') are
     * equivalent if there is a position pi such that s|pi = r and s'|pi = r'.
     */
    public static IntersectorRefPartition fromPositionCorrespondence(final State s1, final State s2) {
        final HeapPositions pos1 = new HeapPositions(s1, true);
        final HeapPositions pos2 = new HeapPositions(s2, true);

        final CollectionMap<AbstractVariableReference, StatePosition> refsAndPos1 = pos1.getReferencesAndPositions();
        for (final Entry<AbstractVariableReference, Collection<StatePosition>> entry : pos1
            .getRefsWithMultiplePositions()
            .entrySet())
        {
            refsAndPos1.add(entry.getKey(), entry.getValue());
        }

        final CollectionMap<AbstractVariableReference, StatePosition> refsAndPos2 = pos2.getReferencesAndPositions();
        for (final Entry<AbstractVariableReference, Collection<StatePosition>> entry : pos2
            .getRefsWithMultiplePositions()
            .entrySet())
        {
            refsAndPos2.add(entry.getKey(), entry.getValue());
        }

        final Set<AbstractVariableReference> refs1 = new LinkedHashSet<>(refsAndPos1.keySet());
        final Set<AbstractVariableReference> refs2 = new LinkedHashSet<>(refsAndPos2.keySet());

        /*
         * For every reference r (including null) in one of the two states s:
         * Create an equivalence class (s, r) -> [(s, r)]
         */
        final Map<StateAndRef, ImmutableSet<StateAndRef>> res = new LinkedHashMap<>();
        IntersectorRefPartition.initializeEqClasses(res, s1, refs1, "s1");
        IntersectorRefPartition.initializeEqClasses(res, s2, refs2, "s2");

        /*
         * For each pair of references r_1, r_2 with s_1|pi = r_1, s_2|pi = r_2
         * add (s_1, r_1) and (s_2, r_2) to the corresponding equivalence
         * classes resulting in (s_1, r_1) -> [(s_1, r_1), (s_2, r_2)] and
         *                      (s_2, r_2) -> [(s_1, r_1), (s_2, r_2)].
         *
         * If the position pi leads through a changed reference in s_2, we do
         * not change the equivalence classes.
         */
        for (final Entry<AbstractVariableReference, Collection<StatePosition>> e : refsAndPos1.entrySet()) {
            final AbstractVariableReference ref = e.getKey();
            final Collection<StatePosition> refPoses = e.getValue();

            // is there a reference in s2 with the same position pi?
            for (final StatePosition pi : refPoses) {
                final AbstractVariableReference otherRef = pos2.getReferenceForPos(pi, true);
                if (otherRef != null) {
                    IntersectorRefPartition.addToEquivalenceClass(res, s1, ref, s2, otherRef);
                }
            }
        }

        for (final Entry<AbstractVariableReference, Collection<StatePosition>> e : refsAndPos2.entrySet()) {
            final AbstractVariableReference ref = e.getKey();
            final Collection<StatePosition> refPoses = e.getValue();

            for (final StatePosition pi : refPoses) {

                final AbstractVariableReference otherRef = pos1.getReferenceForPos(pi, true);
                if (otherRef != null) {
                    IntersectorRefPartition.addToEquivalenceClass(res, s2, ref, s1, otherRef);
                }
            }
        }

        /*
         * We need to sort them to get the intersector to behave nicely (we need
         * the integer references to be present when we create concrete arrays):
         */
        final List<ImmutableSet<StateAndRef>> eqClasses = new ArrayList<>(res.size());
        eqClasses.addAll(res.values());

        Collections.sort(eqClasses, new Comparator<ImmutableSet<StateAndRef>>() {
            @Override
            public int compare(final ImmutableSet<StateAndRef> c1, final ImmutableSet<StateAndRef> c2) {
                //Only look at first refs:
                final AbstractVariableReference oneRef = c1.iterator().next().y;
                final AbstractVariableReference twoRef = c2.iterator().next().y;
                if (!oneRef.pointsToReferenceType() && twoRef.pointsToReferenceType()) {
                    return -1;
                } else if (oneRef.pointsToReferenceType() && !twoRef.pointsToReferenceType()) {
                    return 1;
                }
                return oneRef.toString().compareTo(twoRef.toString());
            }
        });

        res.clear();
        for (final ImmutableSet<StateAndRef> eqClass : eqClasses) {
            for (final StateAndRef p : eqClass) {
                res.put(p, eqClass);
            }
        }

        return new IntersectorRefPartition(ImmutableCreator.create(res));
    }

    /**
     * @param eqClasses map used to compute the equivalence classes
     * @param s some states
     * @param refs set of references in <code>s</code>
     * @param stateDescription a readable name for the state, just for debugging
     */
    public static void initializeEqClasses(
        final Map<StateAndRef, ImmutableSet<StateAndRef>> eqClasses,
        final State s,
        final Set<AbstractVariableReference> refs,
        final String stateDescription)
    {
        //We always want to have the null pointer in the partition:
        refs.add(AbstractVariableReference.NULLREF);
        for (final AbstractVariableReference ref : refs) {
            final StateAndRef p = new StateAndRef(s, ref, stateDescription);
            eqClasses.put(p, ImmutableCreator.create(Collections.singleton(p)));
        }
    }

    /**
     * Add state/reference pair to the equivalence class for another
     * state/reference pair.
     * @param eqClasses map used to compute the equivalence classes
     * @param s1 some state
     * @param r1 some reference in <code>s1</code>
     * @param s2 some state
     * @param r2 some reference in <code>s2</code>
     */
    private static void addToEquivalenceClass(
        final Map<StateAndRef, ImmutableSet<StateAndRef>> eqClasses,
        final State s1,
        final AbstractVariableReference r1,
        final State s2,
        final AbstractVariableReference r2)
    {
        final StateAndRef p1 = new StateAndRef(s1, r1);
        final StateAndRef p2 = new StateAndRef(s2, r2);
        final ImmutableSet<StateAndRef> eqClass1 = eqClasses.get(p1);
        final ImmutableSet<StateAndRef> eqClass2 = eqClasses.get(p2);

        final Set<StateAndRef> newEqClass = new LinkedHashSet<>();
        newEqClass.addAll(eqClass1);
        newEqClass.addAll(eqClass2);

        final ImmutableSet<StateAndRef> immutableNewEqClass = ImmutableCreator.create(newEqClass);

        for (final StateAndRef p : newEqClass) {
            eqClasses.put(p, immutableNewEqClass);
        }
    }

    /**
     * @param s1 some state
     * @param s2 some other state
     * @return reference partition in which two references (s,r), (s',r') are
     * equivalent if there is an unchanged input position pi such that there is
     * a non-root position tau such that s|pi tau = r and s'|pi tau = r'. Of
     * that, the transitive-reflexive-symmetric closure is constructed to yield
     * the partition.
     */
    public static IntersectorRefPartition fromIRCorrespondence(final State s1, final State s2) {
        throw new NotYetImplementedException();
    }

    /**
     * @return collection of the equivalence classes in the stored partition.
     */
    public LinkedHashSet<ImmutableSet<StateAndRef>> getEquivalenceClasses() {
        return new LinkedHashSet<>(this.partition.values());
    }

    /**
     * @param s some state
     * @param ref some reference
     * @return equivalence class for the pair (<code>s</code>,<code>ref</code>)
     */
    public ImmutableSet<StateAndRef> getEquivalenceClass(final State s, final AbstractVariableReference ref) {
        return this.partition.get(new StateAndRef(s, ref));
    }

    /**
     * @param eqClass some equivalence class from this partition.
     * @return collection of the equivalence classes in the stored partition.
     */
    public AbstractVariableReference getNewRefFor(final ImmutableSet<StateAndRef> eqClass) {
        return this.freshNames.get(eqClass);
    }

    /**
     * @param s some state.
     * @param ref some reference in <code>s</code>.
     * @return the reference used for the corresponding equivalence class
     */
    public AbstractVariableReference getNewRefFor(final State s, final AbstractVariableReference ref) {
        final ImmutableSet<StateAndRef> eqClass = this.getEquivalenceClass(s, ref);
        final AbstractVariableReference result = this.freshNames.get(eqClass);
        assert (result != null);
        return result;
    }

    /**
     * @param p1 some state/reference pair
     * @param p2 some other state/reference pair
     * @return true iff the two pairs are marked as equivalent
     */
    public boolean areEquivalent(final StateAndRef p1, final StateAndRef p2) {
        return this.partition.get(p1) == this.partition.get(p2);
    }

    /**
     * @param s1 some state
     * @param ref1 some reference in <code>s1</code>
     * @param s2 some other state
     * @param ref2 some reference in <code>s2</code>
     * @return true iff the two references are marked as equivalent
     */
    public boolean areEquivalent(
        final State s1,
        final AbstractVariableReference ref1,
        final State s2,
        final AbstractVariableReference ref2)
    {
        return this.areEquivalent(new StateAndRef(s1, ref1), new StateAndRef(s2, ref2));
    }

    /**
     * Merges the equivalence class with the equivalence class of null
     * @param eqClass some equivalence class
     */
    public void mergeWithNullEquivalenceClass(final ImmutableSet<StateAndRef> eqClass) {
        final State state = eqClass.iterator().next().x;
        final ImmutableSet<StateAndRef> eqClassNull =
            this.partition.get(new StateAndRef(state, AbstractVariableReference.NULLREF));

        assert (eqClassNull != null) : "Broken partition.";

        final Set<StateAndRef> newEqClass = new LinkedHashSet<>();
        newEqClass.addAll(eqClass);
        newEqClass.addAll(eqClassNull);

        final ImmutableSet<StateAndRef> immutableNewEqClass = ImmutableCreator.create(newEqClass);

        final LinkedHashMap<StateAndRef, ImmutableSet<StateAndRef>> newPartition = new LinkedHashMap<>();
        final LinkedHashMap<ImmutableSet<StateAndRef>, AbstractVariableReference> newFreshNameMap =
            new LinkedHashMap<>();

        newFreshNameMap.put(immutableNewEqClass, AbstractVariableReference.NULLREF);
        for (final Entry<StateAndRef, ImmutableSet<StateAndRef>> e : this.partition.entrySet()) {
            final StateAndRef k = e.getKey();
            if (immutableNewEqClass.contains(k)) {
                newPartition.put(k, immutableNewEqClass);
            } else {
                newPartition.put(k, e.getValue());
                newFreshNameMap.put(e.getValue(), this.freshNames.get(e.getValue()));
            }
        }

        this.partition = ImmutableCreator.create(newPartition);
        this.freshNames = ImmutableCreator.create(newFreshNameMap);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        for (final Entry<StateAndRef, ImmutableSet<StateAndRef>> entry : this.partition.entrySet()) {
            sb.append(entry.getKey() + " -" + this.freshNames.get(entry.getValue()) + "> " + entry.getValue() + "\n");
        }

        return sb.toString();
    }

    /**
     * Replace the fresh name of a reference for a given equivalence class because we found it it references a constant
     * number. Without this replacement we could create states with a reference i_42 mapping to the constant number 23,
     * which causes problems.
     * @param eqClass an equivalence class
     * @param newName the new name for the equivalence class
     */
    public void replaceRefFor(final ImmutableSet<StateAndRef> eqClass, final AbstractVariableReference newName) {
        assert (!newName.pointsToReferenceType());
        final LinkedHashMap<ImmutableSet<StateAndRef>, AbstractVariableReference> newFreshNameMap =
            new LinkedHashMap<>(this.freshNames);
        newFreshNameMap.put(eqClass, newName);
        this.freshNames = ImmutableCreator.create(newFreshNameMap);
    }

    /**
     * @param state some state
     * @return the new names for the references in the given state
     */
    public Map<AbstractVariableReference, AbstractVariableReference> getRenaming(final State state) {
        final Map<AbstractVariableReference, AbstractVariableReference> result = new LinkedHashMap<>();
        for (final Entry<ImmutableSet<StateAndRef>, AbstractVariableReference> entry : this.freshNames.entrySet()) {
            for (final StateAndRef stateAndRef : entry.getKey()) {
                if (stateAndRef.x == state) {
                    if (!stateAndRef.y.equals(entry.getValue())) {
                        result.put(stateAndRef.y, entry.getValue());
                    }
                }
            }
        }
        return result;
    }
}
