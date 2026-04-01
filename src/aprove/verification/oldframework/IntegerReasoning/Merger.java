package aprove.verification.oldframework.IntegerReasoning;

/**
 * @author Alexander Weinert
 *
 * Interface for state mergers. An implementation merges two (abstract) states
 * and produces a new (abstract) state that represents the set of states that
 * are represented by either one of the merged states.
 *
 * @param <State> The type of States that can be merged with this Merger
 * @param <Reference> The types of references held by the States
 */
public interface Merger<State, Reference> {
    /**
     * The order of the state arguments is irrelevant to the result, i.e.,
     * merge(s1, s2, x) shall be equal to merge(s2, s1, x'), where x' is the
     * same as x, except for the mapping adapted to the reversed order of the
     * entries of the pairs of equivalence classes.
     *
     * @param lhsState One of the two states to be merged
     * @param rhsState The other of the two states to be merged
     * @param equivalenceClassMapping The mapping from equivalence
     *  classes to references to be used in the resulting state
     * @return A new abstract state that represents the union of states
     *  represented by the input states
     */
    State merge(State lhsState, State rhsState, EquivalenceClassMapping<Reference> equivalenceClassMapping);
}
