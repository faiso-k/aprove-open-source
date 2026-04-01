package aprove.verification.oldframework.Bytecode.Merger;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * A MergeResult gives information about the three states involved in the
 * merging process (origin + partner = resultState) and the cost of this
 * operation. In case no change to partner was needed to construct the result,
 * this is noted and can be used to draw an instance edge from origin to the
 * partner.
 * @author cotto
 */
public class JBCMergeResult {
    /**
     * When looking for INSTANCE edges we can abort as soon as the information
     * of other must be changed in order to be an instance of the merged state.
     */
    public static final JBCMergeResult FIND_INSTANCE_EDGE = new JBCMergeResult(0., true);

    /**
     * On every update to this MergeResult compare to the stored MergeResult and
     * throw a TooExpensiveException if necessary.
     */
    private JBCMergeResult bestKnownMergeResult;

    /**
     * Cost that is only regarded if the partner state is changed during
     * merging.
     */
    private double conditionalCost;

    /**
     * The cost (difference) of this merging operation.
     */
    private double costOfMerging;

    /**
     * The heap positions for the "left" state.
     */
    private HeapPositions heapPosA;

    /**
     * The heap positions for the "right" state.
     */
    private HeapPositions heapPosB;

    /**
     * The heap positions for the merged state.
     */
    private HeapPositions heapPosC;

    /**
     * This value is true if it was not needed to change anything in the partner
     * state to result in the merged state.
     */
    private boolean partnerEqualsResult;

    /**
     * The partner state used to obtain the merged state.
     */
    private State partnerState;

    /**
     * The origin and partner states are merged into this resultState (may be
     * identical to the origin/partner state).
     */
    private final State resultState;

    /**
     * A helper object to handle the variable references.
     */
    private VariableCache varCache;

    /**
     * Set only if we are in a refineReversible check. If set, this is the
     * reference that is the replacement reference in an equality refinement.
     */
    private final AbstractVariableReference replacementRef;

    /**
     * Set only if we are in a refineReversible check. If set, this is the
     * reference that is the replaced reference in an equality refinement.
     */
    private final AbstractVariableReference replacedRef;

    /**
     * Remember which references where lost due to enforced abstraction.
     */
    private final Collection<AbstractVariableReference> lostReferences;

    /**
     * The interesting references in the partner state.
     */
    private Set<AbstractVariableReference> interestingPartnerRefs;

    /**
     * If false, we do not want to increase the counters of AbstractIntervals during the merge.
     */
    private final boolean increaseCounters;

    /**
     * A set of references for which we only have abstract information in the merged state, but more detailled
     * information in the input states.
     */
    private final Collection<AbstractVariableReference> forcedAbstractions;

    /**
     * A set of references which are successors of some reference we need to abstract.
     */
    private final Collection<AbstractVariableReference> forcedAbstractionsSuccessors;

    /**
     * Create a MergeResult that, in fact, is no result at all.
     */
    public JBCMergeResult() {
        this(Double.POSITIVE_INFINITY, false);
    }

    /**
     * When looking for incoming INSTANCE edges (so using the reverse mode) we
     * can abort as soon as the information of origin must be changed in order
     * to be an instance of the merged state. Mind the swapping! :)
     * @param cost the cost for merging
     * @param partnerEqualsRes true iff the other state is equal to the merged
     * state
     */
    public JBCMergeResult(final Double cost, final boolean partnerEqualsRes) {
        this.varCache = null;
        this.partnerState = null;
        this.resultState = null;
        this.partnerEqualsResult = partnerEqualsRes;
        this.costOfMerging = cost;
        this.replacementRef = null;
        this.replacedRef = null;
        this.lostReferences = new LinkedHashSet<>();
        this.increaseCounters = true;
        this.forcedAbstractions = new LinkedHashSet<>();
        this.forcedAbstractionsSuccessors = new LinkedHashSet<>();
    }

    /**
     * Create a new mergeResult. It is noted if the other state is identical to
     * the merged state.
     * @param partner the other state to compare with
     * @param partnerEqualsRes true iff the other state is equal to the merged
     * state
     * @param bestKnownMergeRes a MergeResult to compare with on every update.
     * @param increaseCountersParam if false, we do not increase the counters of AbstractIntervals
     */
    public JBCMergeResult(
        final State partner,
        final boolean partnerEqualsRes,
        final JBCMergeResult bestKnownMergeRes,
        final boolean increaseCountersParam)
    {
        this(partner, partnerEqualsRes, bestKnownMergeRes, null, null, null, increaseCountersParam);
    }

    /**
     * Create a new mergeResult. It is noted if the other state is identical to
     * the merged state.
     * @param partner the other state to compare with
     * @param partnerEqualsRes true iff the other state is equal to the merged
     * state
     * @param bestKnownMergeRes a MergeResult to compare with on every update.
     * @param replacementRefParam when doing a refine reversible check for an
     * equality refinement, this is the replacement reference (null otherwise).
     * @param replacedRefParam when doing a refine reversible check for an
     * equality refinement, this is the replaced reference (null otherwise).
     * @param interestPartnerRefs the interesting references in state <code>partner</code>
     * @param increaseCountersParam if false, we do not increase the counters of AbstractIntervals
     */
    public JBCMergeResult(
        final State partner,
        final boolean partnerEqualsRes,
        final JBCMergeResult bestKnownMergeRes,
        final AbstractVariableReference replacementRefParam,
        final AbstractVariableReference replacedRefParam,
        final Set<AbstractVariableReference> interestPartnerRefs,
        final boolean increaseCountersParam)
    {
        this.partnerState = partner;
        this.resultState = new State(partner.getClassPath(), partner.getTerminationGraph());
        this.varCache = new VariableCache();
        this.costOfMerging = 0.;
        this.partnerEqualsResult = partnerEqualsRes;
        this.interestingPartnerRefs = interestPartnerRefs;
        this.replacementRef = replacementRefParam;
        this.replacedRef = replacedRefParam;
        if (!partnerEqualsRes) {
            this.partnerState = null;
        }
        if (bestKnownMergeRes == null) {
            this.bestKnownMergeResult = new JBCMergeResult();
        } else {
            this.bestKnownMergeResult = bestKnownMergeRes;
            bestKnownMergeRes.bestKnownMergeResult = null;
            bestKnownMergeRes.varCache = null;
            this.heapPosA = bestKnownMergeRes.heapPosA;
        }
        this.lostReferences = new LinkedHashSet<>();
        this.increaseCounters = increaseCountersParam;
        this.forcedAbstractions = new LinkedHashSet<>();
        this.forcedAbstractionsSuccessors = new LinkedHashSet<>();
    }

    /**
     * Add the given cost only if the partner state is changed.
     * @param addCost some cost to add
     * @param leftRef the causing reference in the left state
     * @param rightRef the causing reference in the right state
     * @param factor Factor with which the costs are scaled before being added to the result (usually depends on the
     *  position of the changed reference)
     * @throws TooExpensiveException if the result is too expensive
     */
    public void addConditionalCost(
        final CostType addCost,
        final AbstractVariableReference leftRef,
        final AbstractVariableReference rightRef,
        final double factor) throws TooExpensiveException
    {
        if (addCost == null) {
            return;
        }
        if (this.interestingPartnerRefs != null && !(this.interestingPartnerRefs.contains(rightRef))) {
            return;
        }
        if (!this.partnerEqualsResult) {
            this.addCost(addCost, Collections.singleton(leftRef), Collections.singleton(rightRef), factor, false);
        } else {
            this.conditionalCost += addCost.getCostValue();
        }
    }

    /**
     * Add the given cost the the current cost.
     * @param addCost the cost to add
     * @param leftRef the reference w.r.t. information was lost
     * @param rightRef the other reference
     * @throws TooExpensiveException if the result is too expensive
     */
    public void addCost(
        final CostType addCost,
        final AbstractVariableReference leftRef,
        final AbstractVariableReference rightRef) throws TooExpensiveException
    {
        this.addCost(addCost, Collections.singleton(leftRef), Collections.singleton(rightRef), 1, false);
    }

    /**
     * Add the given cost the the current cost.
     * @param addCost the cost to add
     * @param leftRefs the references w.r.t. information was lost
     * @param rightRefs the other references
     * @throws TooExpensiveException if the result is too expensive
     */
    public void addCost(
        final CostType addCost,
        final Collection<AbstractVariableReference> leftRefs,
        final Collection<AbstractVariableReference> rightRefs) throws TooExpensiveException
    {
        this.addCost(addCost, leftRefs, rightRefs, 1, false);
    }

    /**
     * Add the given cost the the current cost.
     * @param addCost the cost to add
     * @param leftRef the reference w.r.t. information was lost
     * @param rightRef the other reference
     * @param otherChanged set this to true to denote that the merged state now
     * differs from 'other'
     * @throws TooExpensiveException if the result is too expensive
     */
    public void addCost(
        final CostType addCost,
        final AbstractVariableReference leftRef,
        final AbstractVariableReference rightRef,
        final boolean otherChanged) throws TooExpensiveException
    {
        this.addCost(addCost, Collections.singleton(leftRef), Collections.singleton(rightRef), 1, otherChanged);
    }

    /**
     * Add the given cost the the current cost.
     * @param addCost the cost to add
     * @param leftRefs the references w.r.t. information was lost
     * @param rightRefs the other references
     * @param factor Factor with which the costs are scaled before being added to the result (usually depends on the
     *  position of the changed reference)
     * @param otherChanged set this to true to denote that the merged state now
     * differs from 'other'
     * @throws TooExpensiveException if the result is too expensive
     */
    public void addCost(
        final CostType addCost,
        final Collection<AbstractVariableReference> leftRefs,
        final Collection<AbstractVariableReference> rightRefs,
        final double factor,
        final boolean otherChanged) throws TooExpensiveException
    {

        boolean anyInteresting = true;
        if (this.interestingPartnerRefs != null) {
            anyInteresting = false;
            if (otherChanged) {
                for (final AbstractVariableReference rightRef : rightRefs) {
                    anyInteresting |= this.interestingPartnerRefs.contains(rightRef);
                }
            } else {
                for (final AbstractVariableReference leftRef : leftRefs) {
                    anyInteresting |= this.interestingPartnerRefs.contains(leftRef);
                }
            }
        }

        if (!anyInteresting) {
            return;
        }

        if (otherChanged) {
            this.setOtherChanged();
        }

        this.costOfMerging += factor * addCost.getCostValue();
        if (this.isMoreExpensive(this.bestKnownMergeResult)) {
            throw new TooExpensiveException("Old result is strictly better than new result:\nOld:\n"
                + this.bestKnownMergeResult.getCost()
                + "\nNew:\n"
                + this.getCost());
        }
    }

    /**
     * Transfer the conditional cost, if needed.
     * @throws TooExpensiveException if the result is too expensive
     */
    private void checkConditional() throws TooExpensiveException {
        if (!this.partnerEqualsResult) {
            this.costOfMerging += this.conditionalCost;
            this.conditionalCost = 0;
        }
    }

    /**
     * @param other Another merge result we are comparing to.
     * @return false if this result is considered to be better than the other result. false is returned for identical
     * cost, true is returned if the other state is cheaper.
     */
    public boolean isMoreExpensive(final JBCMergeResult other) {
        assert (other != null);
        final double otherCost = other.costOfMerging;
        if (this.partnerEqualsResult) {
            if (!other.partnerEqualsResult) {
                // this is a better result, as we can draw an outgoing INSTANCE
                // edge.
                return false;
            }
            // if both results permit an outgoing INSTANCE edge, use
            // the one to the more general state. This means we chose the
            // more expensive result!
            return Double.compare(this.costOfMerging, otherCost) < 0;
        }
        // no outgoing INSTANCE edge is possible with this result
        if (other.partnerEqualsResult) {
            // the other result allows an outgoing INSTANCE edge!
            return true;
        }
        // just take the minimal cost
        return Double.compare(this.costOfMerging, otherCost) > 0;
    }

    /**
     * Create information about the heap positions for all involved states
     * @param thatState the 'left' state
     * @param thisState the 'right' state
     * @param mergedState the resulting merged state
     */
    public void createHeapPositions(final State thisState, final State thatState, final State mergedState) {
        if (this.heapPosA == null && thisState != null) {
            this.heapPosA = new HeapPositions(thisState);
        }
        if (this.heapPosB == null && thatState != null) {
            this.heapPosB = new HeapPositions(thatState);
        }
        if (this.heapPosC == null && mergedState != null) {
            this.heapPosC = new HeapPositions(mergedState);
        }
    }

    /**
     * @return the cost of the merging process.
     */
    public double getCost() {
        return this.costOfMerging;
    }

    /**
     * @param returnHeapPosA true iff heapPosA should be returned
     * @return heapPosA or heapPosB
     */
    public HeapPositions getHeapPositions(final boolean returnHeapPosA) {
        if (returnHeapPosA) {
            assert (this.heapPosA != null);
            return this.heapPosA;
        }
        assert (this.heapPosB != null);
        return this.heapPosB;
    }

    /**
     * @return heap positions A
     */
    public HeapPositions getHeapPositionsA() {
        assert (this.heapPosA != null);
        return this.heapPosA;
    }

    /**
     * @return heap positions B
     */
    public HeapPositions getHeapPositionsB() {
        assert (this.heapPosB != null);
        return this.heapPosB;
    }

    /**
     * @return heap positions C
     */
    public HeapPositions getHeapPositionsC() {
        assert (this.heapPosC != null);
        return this.heapPosC;
    }

    /**
     * @param refA a reference
     * @param refB another reference
     * @return the cached result of merging the two given variables (if known).
     */
    public AbstractVariableReference getMergedReference(
        final AbstractVariableReference refA,
        final AbstractVariableReference refB)
    {
        return this.varCache.get(refA, refB);
    }

    /**
     * @return the state resulting out of merging the origin state and some
     * other state.
     */
    public State getMergedState() {
        return this.resultState;
    }

    /**
     * @return The partner state used to obtain the merged state.
     */
    public State getPartnerState() {
        return this.partnerState;
    }

    /**
     * @return the varCache
     */
    public VariableCache getVarCache() {
        return this.varCache;
    }

    /**
     * @return true iff the cost of merging isn't the absolute smallest value.
     */
    public boolean isValid() {
        try {
            this.checkConditional();
        } catch (final TooExpensiveException e) {
            return false;
        }
        return !Double.isInfinite(this.costOfMerging);
    }

    /**
     * @return true iff the other state equals the merged state.
     */
    public boolean partnerEqualsMergedState() {
        return this.partnerEqualsResult;
    }

    /**
     * Denote that the merged state now differs from 'other'.
     * @throws TooExpensiveException if the result is too expensive
     */
    public void setOtherChanged() throws TooExpensiveException {
        if (this.partnerEqualsResult) {
            this.partnerEqualsResult = false;
            this.checkConditional();
            if (this.isMoreExpensive(this.bestKnownMergeResult)) {
                throw new TooExpensiveException("Old result is strictly better than new result:\nOld:\n"
                    + this.bestKnownMergeResult.getCost()
                    + "\nNew:\n"
                    + this.getCost());
            }
        }
    }

    /**
     * Remember that the result of merging refA with refB is resRef.
     * @param refA a reference
     * @param refB another reference
     * @param resRef the resulting reference
     */
    public void store(
        final AbstractVariableReference refA,
        final AbstractVariableReference refB,
        final AbstractVariableReference resRef)
    {
        this.store(refA, refB, resRef, null);
    }

    /**
     * Remember that the result of merging refA with refB is resRef.
     * @param refA a reference
     * @param refB another reference
     * @param resRef the resulting reference
     * @param pos the state position where we merged
     */
    public void store(
        final AbstractVariableReference refA,
        final AbstractVariableReference refB,
        final AbstractVariableReference resRef,
        final StatePosition pos)
    {
        this.varCache.store(refA, refB, resRef, pos);
    }

    /**
     * @return the replacement reference when doing a equality refinement (set
     * when doing a refine reversible check)
     */
    public AbstractVariableReference getReplacementReference() {
        return this.replacementRef;
    }

    /**
     * @return the replaced reference when doing a equality refinement (set when
     * doing a refine reversible check)
     */
    public AbstractVariableReference getReplacedRef() {
        return this.replacedRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        if (this.partnerEqualsResult) {
            sb.append("Partner=Result!\n");
        }
        sb.append("Cost: ");
        sb.append(this.costOfMerging);
        if (this.partnerState != null) {
            sb.append("\n\nPartner state:\n");
            sb.append(this.partnerState.toString());
        }
        if (this.resultState != null) {
            sb.append("\n\nMerged state:\n");
            sb.append(this.resultState.toString());
        }
        sb.append("\n");
        return sb.toString();
    }

    /**
     * Remember which references were lost due to enforced abstraction.
     * @param references a set of references
     */
    public void addLostReferences(final Collection<AbstractVariableReference> references) {
        this.lostReferences.addAll(references);
    }

    /**
     * @return the lost references
     */
    public Collection<AbstractVariableReference> getLostReferences() {
        return this.lostReferences;
    }

    /**
     * @param pos Heap position at which the indicated cost is incurred.
     * @return factor used to scale costs depending on the state position at which it was incurred.
     */
    public static double getCostFactor(final StatePosition pos) {
        return 1.0 / pos.length();
    }

    /**
     * @return false only if we do not want to increae the counters of AbstractIntervals during the merge
     */
    public boolean getIncreaseCounters() {
        return this.increaseCounters;
    }

    /**
     * @return the set of references which we abstracted although the input states have more detailled information
     */
    public Collection<AbstractVariableReference> getForcedAbstractions() {
        return this.forcedAbstractions;
    }

    /**
     * @return the set of references which are successors of some reference we need to abstract
     */
    public Collection<AbstractVariableReference> getForcedAbstractionsSuccessors() {
        return this.forcedAbstractionsSuccessors;
    }

    /**
     * @return true if we only look for instances, i. e. we abort as soon as the partner needs to be changed
     */
    public boolean onlyFindInstance() {
        return this.bestKnownMergeResult != null && this.bestKnownMergeResult == JBCMergeResult.FIND_INSTANCE_EDGE;
    }
}
