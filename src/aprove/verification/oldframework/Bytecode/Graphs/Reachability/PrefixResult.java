package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * When asking for the maximal realized prefix of some state position, we
 * need some additional information. This is stored using this class. Here,
 * for non-realized suffixes "acyclic" means that cycles that may be
 * traversed starting somewhere in the non-realized suffix (including nested
 * cycles) are not represented. As a consequence, the cycles must be
 * manually regarded when all possible paths (and the corresponding set of
 * heap edges!) is computed.
 * @author cotto
 */
public class PrefixResult {
    /**
     * The reference at the maximal realized part of the position.
     */
    private final AbstractVariableReference reference;

    /**
     * The position leading to the reference.
     */
    private final StatePosition position;

    /**
     * Set if the position originally asked for is fully realized.
     */
    private final boolean isRealized;

    /**
     * For unrealized prefixes, this contains the (acyclic) suffix that is
     * missing from the original target position.
     */
    private final StatePosition unrealizedPosition;

    /**
     * @param ref the reference which is at the end of the realized part of
     * the state position (not fully realized).
     * @param posParam the position leading to the reference
     * @param unrealizedPositionParam the (acyclic) part of the position
     * that is not realized
     */
    public PrefixResult(final AbstractVariableReference ref,
            final StatePosition posParam,
            final StatePosition unrealizedPositionParam) {
        assert (ref != null);
        assert (posParam != null || ref.isNULLRef());
        this.reference = ref;
        this.position = posParam;
        this.isRealized = false;
        if (!this.reference.isNULLRef() && unrealizedPositionParam != null) {
            assert (unrealizedPositionParam instanceof NonRootPosition);
        }
        this.unrealizedPosition = unrealizedPositionParam;
    }

    /**
     * @param ref the reference which is at the end of the state position,
     * fully realized (unrealized in case the reached reference is the null
     * reference).
     * @param posParam the position leading to the reference
     */
    public PrefixResult(final AbstractVariableReference ref,
            final StatePosition posParam) {
        assert (ref != null);
        assert (posParam != null);
        this.reference = ref;
        this.position = posParam;
        assert (!this.reference.isNULLRef());
        this.isRealized = true;
        this.unrealizedPosition = null;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder();
        result.append(this.reference.toString());
        result.append(" ");
        if (this.position != null) {
            this.position.toString(result);
        }
        if (!this.isRealized()) {
            result.append(" ! ");
        }
        if (this.unrealizedPosition != null) {
            this.unrealizedPosition.toString(result);
        }
        return result.toString();
    }

    /**
     * @return the reference
     */
    public AbstractVariableReference getReference() {
        return this.reference;
    }

    /**
     * @return true iff the position is fully realized
     */
    public boolean isRealized() {
        return this.isRealized;
    }

    /**
     * @return the position leading to the reference
     */
    public StatePosition getPosition() {
        return this.position;
    }

    /**
     * @param that some prefix result
     * @return true iff the two prefix results have the same suffix
     */
    public boolean sameSuffix(final PrefixResult that) {
        if (this.isRealized() != that.isRealized()) {
            return false;
        }
        if (this.unrealizedPosition == null) {
            return that.unrealizedPosition == null;
        }
        return this.unrealizedPosition.equals(that.unrealizedPosition);
    }

    /**
     * @return the position that is not realized
     */
    public StatePosition getUnrealizedPosition() {
        return this.unrealizedPosition;
    }
}
