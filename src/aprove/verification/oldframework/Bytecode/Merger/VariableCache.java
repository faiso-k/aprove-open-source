package aprove.verification.oldframework.Bytecode.Merger;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * When merging two states an instance of this class can be used to cache
 * results.
 * @author cotto
 */
public class VariableCache {
    /**
     * The known references are stored here.
     */
    private final Map<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference> map;

    /**
     * Create a new variable cache for the three given states.
     */
    public VariableCache() {
        this.map = new LinkedHashMap<>();
    }

    public boolean contains(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        return this.map.containsKey(new Pair<>(refA, refB));
    }

    /**
     * For two given variable references the resulting abstract reference is
     * returned (if known).
     * @param refA a reference to a variable in the first state
     * @param refB a reference to a variable in the second state
     * @return a reference to the merged variable if this is known, null
     * otherwise.
     */
    public AbstractVariableReference get(final AbstractVariableReference refA, final AbstractVariableReference refB) {
        return this.get(new Pair<>(refA, refB));
    }

    /**
     * For two given variable references the resulting abstract reference is
     * returned (if known).
     * @param refA a reference to a variable in the first state
     * @param refB a reference to a variable in the second state
     * @param fromLeft true iff refA is the left and refB the right partner.
     * @return a reference to the merged variable if this is known, null
     * otherwise.
     */
    public AbstractVariableReference get(final AbstractVariableReference refA,
        final AbstractVariableReference refB,
        final boolean fromLeft) {
        if (fromLeft) {
            return this.get(refA, refB);
        }
        return this.get(refB, refA);
    }

    /**
     * For two given variable references the resulting abstract reference is
     * returned (if known).
     * @param pair a pair of two references to variables in the first and second
     * state.
     * @return a reference to the merged variable if this is known.
     */
    public AbstractVariableReference get(final Pair<AbstractVariableReference, AbstractVariableReference> pair) {
        return this.map.get(pair);
    }

    /**
     * @return the entry set to the map defining this variable cache.
     */
    public Set<Map.Entry<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference>> getEntrySet() {
        return this.map.entrySet();
    }

    /**
     * @param x a reference
     * @param y another reference
     * @param fromLeft true iff x, y are left partners in the merge.
     * @return { merge partners of x } \times { merge partners of y }
     */
    public Set<Pair<AbstractVariableReference, AbstractVariableReference>> getMergePartnerPairs(final AbstractVariableReference x,
        final AbstractVariableReference y,
        final boolean fromLeft) {

        final Set<Pair<AbstractVariableReference, AbstractVariableReference>> res = new LinkedHashSet<>();

        if (fromLeft) {
            for (final AbstractVariableReference xMergePartner : this.getPartnersForLeft(x)) {
                for (final AbstractVariableReference yMergePartner : this.getPartnersForLeft(y)) {
                    res.add(new Pair<>(xMergePartner, yMergePartner));
                }
            }
        } else {
            for (final AbstractVariableReference xMergePartner : this.getPartnersForRight(x)) {
                for (final AbstractVariableReference yMergePartner : this.getPartnersForRight(y)) {
                    res.add(new Pair<>(xMergePartner, yMergePartner));
                }
            }
        }

        return res;
    }

    /**
     * @param ref a reference
     * @param fromLeft true iff refA should be the left partner
     * @return all references that are stored as right partner for some pair (refA, ...) (or, iff fromLeft is false, for (..., refA)).
     */
    public Set<AbstractVariableReference> getPartners(final AbstractVariableReference ref, final boolean fromLeft) {
        if (fromLeft) {
            return this.getPartnersForLeft(ref);
        }
        return this.getPartnersForRight(ref);
    }

    /**
     * @param refA a reference
     * @return all references that are stored as right partner for some pair (refA, ...).
     */
    public Set<AbstractVariableReference> getPartnersForLeft(final AbstractVariableReference refA) {
        final Set<AbstractVariableReference> result = new LinkedHashSet<>();
        if (refA != null) {
            for (final Pair<AbstractVariableReference, AbstractVariableReference> key : this.map.keySet()) {
                if (refA.equals(key.x)) {
                    result.add(key.y);
                }
            }
        }
        return result;
    }

    /**
     * @param refB a reference
     * @return all references that are stored as left partner for some pair (..., refB).
     */
    public Set<AbstractVariableReference> getPartnersForRight(final AbstractVariableReference refB) {
        final Set<AbstractVariableReference> result = new LinkedHashSet<>();
        if (refB != null) {
            for (final Pair<AbstractVariableReference, AbstractVariableReference> key : this.map.keySet()) {
                if (refB.equals(key.y)) {
                    result.add(key.x);
                }
            }
        }
        return result;
    }

    /**
     * @param ref a reference
     * @param fromLeft true iff ref is left partner of the merge
     * @return all references that are stored for some pair (ref, ...) (or, iff fromLeft is false, for some pair (..., ref)).
     */
    public Set<AbstractVariableReference> getResults(final AbstractVariableReference ref, final boolean fromLeft) {
        final Set<AbstractVariableReference> result = new LinkedHashSet<>();
        if (fromLeft) {
            for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : this.getResultsForLeft(ref)) {
                result.add(pair.x);
            }
            return result;
        }
        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : this.getResultsForRight(ref)) {
            result.add(pair.x);
        }
        return result;
    }

    /**
     * @param refA a reference
     * @return a list where for each (refA, refB) -> resRef the pair (resRef,
     * refB) is added.
     */
    public List<Pair<AbstractVariableReference, AbstractVariableReference>> getResultsForLeft(final AbstractVariableReference refA) {
        final List<Pair<AbstractVariableReference, AbstractVariableReference>> result = new LinkedList<>();
        assert (refA != null);
        for (final Map.Entry<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference> entry : this.map.entrySet()) {
            if (refA.equals(entry.getKey().x)) {
                result.add(new Pair<>(entry.getValue(), entry.getKey().y));
            }
        }
        return result;
    }

    /**
     * @param refB a reference
     * @return a list where for each (refA, refB) -> resRef the pair (resRef,
     * refA) is added.
     */
    public List<Pair<AbstractVariableReference, AbstractVariableReference>> getResultsForRight(final AbstractVariableReference refB) {
        final List<Pair<AbstractVariableReference, AbstractVariableReference>> result = new LinkedList<>();
        if (refB != null) {
            for (final Map.Entry<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference> entry : this.map.entrySet()) {
                if (refB.equals(entry.getKey().y)) {
                    result.add(new Pair<>(entry.getValue(), entry.getKey().x));
                }
            }
        }
        return result;
    }

    /**
     * Store the given reference as the result for merging the other two
     * references.
     * @param refA a reference to a variable in the first state
     * @param refB a reference to a variable in the second state
     * @param resRef the resulting reference
     * @param pos the position of the three references
     */
    public void store(final AbstractVariableReference refA,
        final AbstractVariableReference refB,
        final AbstractVariableReference resRef,
        final StatePosition pos) {
        this.store(new Pair<>(refA, refB), resRef, pos);
    }

    /**
     * Store the given reference as the result for merging the other two
     * references.
     * @param pair two references to variables in the first and second state
     * @param resRef the resulting reference
     * @param pos the position of the three references
     */
    private void store(final Pair<AbstractVariableReference, AbstractVariableReference> pair,
        final AbstractVariableReference resRef,
        final StatePosition pos) {
        final AbstractVariableReference ret = this.map.put(pair, resRef);
        assert (ret == null || ret.equals(resRef));
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder sbRef = new StringBuilder();
        final StringBuilder sbNonRef = new StringBuilder();
        for (final Map.Entry<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference> entry : this.map.entrySet()) {
            StringBuilder sb;
            if (entry.getValue().pointsToReferenceType()) {
                sb = sbRef;
            } else {
                sb = sbNonRef;
            }
            sb.append(entry.toString());
            sb.append("\n");
        }
        return sbRef.append(sbNonRef).toString();
    }
}
