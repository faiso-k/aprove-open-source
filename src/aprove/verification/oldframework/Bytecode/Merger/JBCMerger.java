package aprove.verification.oldframework.Bytecode.Merger;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * <p>
 * A "merger" can be used to merge two states (A and B) into another one (C), such that C covers all possible
 * computations that are defined in A or B. In other words, A and B are instances of C. If one needs to find such a
 * state C, it is desirable to do as little abstraction as possible compared to A and B. Therefore, we fix A and try all
 * possible candidates B. During this computation only the best combination of (A, B, C) is remembered, such that -
 * after trying all candidates for B - the abstraction needed to create C is minimal in some sense. Each implementation
 * should abort computations with a B candidate, if the best known result already is strictly better. If one finds a
 * state B such that A is an instance of B, this results in B=C (up to renaming). In this situation, which is indicated
 * by the result, the already existing state B should be preferred over C.
 * </p>
 * <p>
 * The basic functionality, finding a state C such that A and some B are instances of C, can be achieved by using the
 * constructor only taking state A and providing the B candidates using 'merge(B)'.
 * </p>
 * <p>
 * <p>
 * The merger can also be used to find out which of the B states are instances of the given state A. Here, instead of
 * computing the best C and then looking at the cost to found out if B is an instance of A, it is desirable to limit the
 * merger to results with no cost (meaning instances). This approach can also be used for arbitrary cost that may arise
 * due to some heuristics. The constructor taking a second argument of type Integer can be used to private this cost
 * limit.
 * <p>
 * <p>
 * If one needs to find out if X is an instance of Y, the method 'isInstance(X, Y)' and the constructor without
 * arguments can be used.
 * </p>
 * @author Carsten Otto
 * @see {@link PathMerger}
 */
public interface JBCMerger {
    /**
     * This abstract class provides the basic functionality every merger offers.
     * @author cotto
     */
    public abstract class JBCMergerSkeleton implements JBCMerger {
        /**
         * If false, we do not increase the counters of AbstractIntervals during the merge.
         */
        private boolean increaseCounters = true;

        /**
         * A.
         */
        private final State aState;

        /**
         * This object gives the result of the merging process, including all three states and the associated cost. The
         * result also includes the information, whether A is an instance of B.
         * @see JBCMerger#getResult()
         */
        private JBCMergeResult mergeResult;

        /**
         * Provide an instance of this merger so that 'isInstance(A, B)' can be used. Here, the abstraction needed to
         * generate C is minimized.
         * @see JBCMerger#isInstance(State, State)
         */
        public JBCMergerSkeleton() {
            this.aState = null;
        }

        /**
         * Merge A with given states B such that A and B are instances of the resulting state C.
         * @see JBCMerger#merge(State)
         * @param a A
         */
        public JBCMergerSkeleton(final State a) {
            this(a, null);
        }

        /**
         * Find a state C for the given state A and the B candidates, such that A and B are instances of C. Here, the
         * abstraction needed to generate C is minimized. Furthermore, only results with cost not exceeding the given
         * maximum are returned.
         * @see JBCMerger#isInstance(State, State) to only find out if one state is an instance of the other state.
         * @param a A
         * @param maximalCosts If null, enforces a merge. If <= 0, only finds states of which <code>A</code> is an
         * instance of. If > 0, finds states where the needed abstraction is limited.
         */
        public JBCMergerSkeleton(final State a, final Double maximalCosts) {
            this.aState = a;
            if (maximalCosts == null) {
                /*
                 * Start with the worst merge result of all times, which is not
                 * valid at all. This is used to find any state C.
                 */
                this.mergeResult = new JBCMergeResult();
            } else if (maximalCosts <= 0) {
                /*
                 * start with the result that is better than every result where no
                 * outgoing instance edge can be drawn
                 */
                this.mergeResult = JBCMergeResult.FIND_INSTANCE_EDGE;
            } else {
                /*
                 * Pass the cost through so that only merge partners which are
                 * somehow similar to originState are found.
                 */
                this.mergeResult = new JBCMergeResult(maximalCosts, false);
            }
        }

        /**
         * Add a =?= annotation and add costs, if needed.
         * @param ourRef the reference in our state that is at at the same positions as refsOne.y and refsTwo.y and
         *  hence enforces the equality.
         * @param refsOne a pair, where the first component is the reference in the merged state and the other component
         * is the corresponding reference in partnerGraph.
         * @param refsTwo a pair, where the first component is the reference in the merged state and the other component
         * is the corresponding reference in partnerGraph.
         * @param partnerGraph the equality graph of the current partner state
         * @param newResult merge result to add costs to
         * @param fromLeft true iff the partner state is "other"
         * @return true iff the annotation was added
         * @throws TooExpensiveException if adding the annotation is too expensive
         */
        protected static boolean addEqAnnotation(
            final AbstractVariableReference ourRef,
            final Pair<AbstractVariableReference, AbstractVariableReference> refsOne,
            final Pair<AbstractVariableReference, AbstractVariableReference> refsTwo,
            final EqualityGraph partnerGraph,
            final JBCMergeResult newResult,
            final boolean fromLeft) throws TooExpensiveException
        {
            final State mergedState = newResult.getMergedState();
            if (mergedState
                .getHeapAnnotations()
                .getEqualityGraph()
                .addPossibleEquality(mergedState, refsOne.x, refsTwo.x))
            {
                // It seems that this was a new equality, now on to cost computation:
                // Check if in otherState the corresponding were already marked
                // as possibly equal:
                final AbstractVariableReference otherOne = refsOne.y;
                final AbstractVariableReference otherTwo = refsTwo.y;
                if (!otherOne.equals(otherTwo) && !partnerGraph.areMarkedAsPossiblyEqual(otherOne, otherTwo)) {
                    final Set<AbstractVariableReference> eqedRefs = new LinkedHashSet<>();
                    eqedRefs.add(otherOne);
                    eqedRefs.add(otherTwo);

                    newResult.addCost(CostType.LOST_INEQUALITY, Collections.singleton(ourRef), eqedRefs, 1, fromLeft);
                }
                return true;
            }
            return false;
        }

        /**
         * Add equality annotations for merged pairs which need it
         * @param thisState one of the two involved states
         * @param thatState the other state
         * @param newResult the result being constructed
         * @throws TooExpensiveException if merging is aborted.
         */
        protected static void addNewEqualityAnnotations(
            final State thisState,
            final State thatState,
            final JBCMergeResult newResult) throws TooExpensiveException
        {
            final VariableCache varCache = newResult.getVarCache();

            for (final Map.Entry<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference> e : varCache
                .getEntrySet())
            {
                final AbstractVariableReference refA = e.getKey().x;
                final AbstractVariableReference refB = e.getKey().y;

                /*
                 * Now try to find places where we might need to add an =?=:
                 * Find all other merge results which were created from one or the other of
                 * these variables. As they were the same variable in one of the original states,
                 * we should mark that they could be equal in the resulting state.
                 *
                 * The list "left" contains tuples (x, y) where x is the result of
                 * merging refA with y.
                 */
                if (!refA.isNULLRef()) {
                    final List<Pair<AbstractVariableReference, AbstractVariableReference>> left =
                        varCache.getResultsForLeft(refA);

                    JBCMergerSkeleton.createEqualities(refA, left, newResult, thatState, newResult.getMergedState(), true);
                }

                if (!refB.isNULLRef()) {
                    final List<Pair<AbstractVariableReference, AbstractVariableReference>> right =
                        varCache.getResultsForRight(refB);

                    JBCMergerSkeleton.createEqualities(refB, right, newResult, thisState, newResult.getMergedState(), false);
                }
            }
        }

        /**
         * This method is called in the context of a single abstract variable reference and deals with all merge
         * partners of this reference. If the list contains more than one entry, we may need to add a =?= annotation.
         * @param ourRef the reference in our state that is at at the same positions as the refs in <code>list</code>
         * @param list a list containing overlapping merge results
         * @param newResult merge result to add costs to
         * @param partnerState the state where the partner used for the merge resides
         * @param resultState the result of the merge
         * @param fromLeft true iff the other state is the right state
         * @throws TooExpensiveException if adding costs is too expensive
         */
        private static void createEqualities(
            final AbstractVariableReference ourRef,
            final List<Pair<AbstractVariableReference, AbstractVariableReference>> list,
            final JBCMergeResult newResult,
            final State partnerState,
            final State resultState,
            final boolean fromLeft) throws TooExpensiveException
        {
            final int size = list.size();
            if (size < 2) {
                return;
            }

            /*
             * Our input actually is just a part of the variable cache merge table.
             * Let ourRef be some fixed AVR:
             *
             *  someSide  |    partnerRef    |      resRef
             *  ----------+------------------+------------------
             *    ourRef  |  list.get(1).y   |   list.get(1).x
             *    ourRef  |  list.get(2).y   |   list.get(2).x
             *  ...
             *
             * So we want to ensure that all entries in the resRef column are marked
             * as possibly equal (so that we can recreate the original state).
             *
             * We just look at the complete resRef column, build all two-tuples by
             * looking at the upper half and add equalities everywhere.
             */

            final EqualityGraph partnerGraph = partnerState.getHeapAnnotations().getEqualityGraph();
            for (int i = 0; i < size; i++) {
                final Pair<AbstractVariableReference, AbstractVariableReference> pairOne = list.get(i);
                final AbstractVariableReference mergedRefOne = pairOne.x;

                for (int j = i + 1; j < size; j++) {
                    final Pair<AbstractVariableReference, AbstractVariableReference> pairTwo = list.get(j);
                    final AbstractVariableReference mergedRefTwo = pairTwo.x;

                    /*
                     * We lose information about equality. Therefore we need
                     * to introduce some costs to forbid instance edges.
                     *
                     * This can be seen, for example, with integers:
                     *
                     * State 1: x: i1   y: i1   (i1 > 0)
                     * State 2: x: 23   y: 42
                     *
                     * When merging these, we only add costs relative to
                     * State 2 and would allow an instance edge S2->S1. This
                     * is wrong, as in State 1 the expression x == y never gives
                     * "false".
                     *
                     * Originally, the following cost addition was wrapped in a
                     * if (!partnerRefOne.equals(partnerRefTwo)), but that is
                     * unneeded: All rows of the varCache are unique, and the fact
                     * that we are looking at two rows with the same left ref
                     * implies that !partnerRefOne.equals(partnerRefTwo) holds:
                     */
                    if (!(pairOne.y.equals(newResult.getReplacementReference()) && pairTwo.y.equals(newResult
                        .getReplacementReference())))
                    {
                        final Collection<AbstractVariableReference> neqedRefs = new LinkedList<>();
                        neqedRefs.add(pairOne.y);
                        neqedRefs.add(pairTwo.y);
                        newResult.addCost(
                            CostType.LOST_EQUALITY,
                            neqedRefs,
                            Collections.singleton(ourRef),
                            1,
                            !fromLeft);
                    }

                    if (mergedRefTwo.isNULLRef() || mergedRefOne.isNULLRef()) {
                        continue;
                    }

                    JBCMergerSkeleton.addEqAnnotation(ourRef, pairOne, pairTwo, partnerGraph, newResult, fromLeft);
                }
            }
        }

        /**
         * Ensure for all variable references for which we have any equality information that *all* of their
         * counterparts in the merged state also have this information. If the other state had the same information,
         * don't add any cost. See Definition 2f.
         * @param ourEqG Our equality graph
         * @param partnerEqG Partner equality graph
         * @param mergedEqG Merged equality graph
         * @param newResult merge result
         * @param fromLeft Indicate if our state is left merge partner
         * @throws TooExpensiveException if merging is aborted.
         */
        protected static void mergeEqualityGraphs(
            final EqualityGraph ourEqG,
            final EqualityGraph partnerEqG,
            final EqualityGraph mergedEqG,
            final JBCMergeResult newResult,
            final boolean fromLeft) throws TooExpensiveException
        {
            final VariableCache varCache = newResult.getVarCache();
            //For all references in our equality graph ...
            for (final AbstractVariableReference t : ourEqG.getReferences()) {
                //... iterate over all of their direct partners:
                // This gives us all pairs t =?= equalityPartner
                for (final AbstractVariableReference equalityPartner : ourEqG.getPartners(t)) {
                    // For t =?= equalityPartner, find all merge partners refPartner1 and refPartner2
                    for (final Pair<AbstractVariableReference, AbstractVariableReference> mergePartnerPair : varCache
                        .getMergePartnerPairs(t, equalityPartner, fromLeft))
                    {
                        // Now try to add t+refPartner1 =?= equalityPartner+refPartner2 to the merged equality graph
                        // [where + indicates ref-wise merging].
                        final AbstractVariableReference refPartner1 = mergePartnerPair.x;
                        final AbstractVariableReference refPartner2 = mergePartnerPair.y;

                        final AbstractVariableReference mergedRefOne = varCache.get(t, refPartner1, fromLeft);
                        final AbstractVariableReference mergedRefTwo =
                            varCache.get(equalityPartner, refPartner2, fromLeft);

                        final Pair<AbstractVariableReference, AbstractVariableReference> mergedPairOne =
                            new Pair<>(mergedRefOne, refPartner1);
                        final Pair<AbstractVariableReference, AbstractVariableReference> mergedPairTwo =
                            new Pair<>(mergedRefTwo, refPartner2);

                        JBCMergerSkeleton.addEqAnnotation(t, mergedPairOne, mergedPairTwo, partnerEqG, newResult, fromLeft);
                    }
                }
            }
        }

        /**
         * If the two classes have different initialization information, abort. Otherwise, set the information in the
         * merged state.
         * @param thisState one of the two involved states
         * @param thatState the other state
         * @param newResult the result being constructed
         * @throws TooExpensiveException if merging is aborted.
         */
        public static
            void
            mergeInitialization(final State thisState, final State thatState, final JBCMergeResult newResult)
                throws TooExpensiveException
        {
            JBCOptions options = thisState.getJBCOptions();
            final State mergeState;
            if (newResult != null) {
                mergeState = newResult.getMergedState();
            } else {
                mergeState = null;
            }

            final Map<ClassName, InitStatus> thisInitClasses =
                thisState.getClassInitInfo().getClassesWithInitializationState(options);
            final Map<ClassName, InitStatus> thatInitClasses =
                thatState.getClassInitInfo().getClassesWithInitializationState(options);
            final Set<ClassName> initClasses = new LinkedHashSet<>(thisInitClasses.size());
            initClasses.addAll(thisInitClasses.keySet());
            initClasses.addAll(thatInitClasses.keySet());
            for (final ClassName cn : initClasses) {
                final InitStatus thisYNM = thisInitClasses.get(cn);
                final InitStatus thatYNM = thatInitClasses.get(cn);
                if (thisYNM == thatYNM) {
                    if (mergeState != null) {
                        mergeState.getClassInitInfo().setInitialized(cn, thisYNM);
                    }
                    continue;
                } else if (thisYNM == InitStatus.YES && thatYNM == InitStatus.MAYBE) {
                    /*
                     * If initalization of the class that is marked with MAYBE has
                     * no effect at all, there is no difference between MAYBE and
                     * YES. In this case, we can merge (and, to save some effort,
                     * mark the result with YES).
                     */
                    final ClassPath cPath = thisState.getClassPath();
                    final IClass parsedClass = cPath.getClass(cn);
                    if (ObjectRefinement.hasNoopInit(parsedClass, thatInitClasses)) {
                        if (mergeState != null) {
                            mergeState.getClassInitInfo().setInitialized(cn, InitStatus.YES);
                        }
                        continue;
                    }
                } else if (thisYNM == InitStatus.MAYBE && thatYNM == InitStatus.YES) {
                    // see previous case
                    final ClassPath cPath = thisState.getClassPath();
                    final IClass parsedClass = cPath.getClass(cn);
                    if (ObjectRefinement.hasNoopInit(parsedClass, thisInitClasses)) {
                        if (mergeState != null) {
                            mergeState.getClassInitInfo().setInitialized(cn, InitStatus.YES);
                        }
                        continue;
                    }
                }
                throw new TooExpensiveException("Won't merge states with initialization states "
                    + thisYNM
                    + " and "
                    + thatYNM
                    + " for class "
                    + cn);
            }
        }

        /**
         * Merge A with B.
         * @param a A
         * @param b B
         * @param result will be filled with the resulting state "C" and information about the involved cost and whether
         * A is an instance of B.
         * @return true iff a new (better) result was found
         */
        protected abstract boolean computeResult(State a, State b, JBCMergeResult result);

        /**
         * This function may only be called if at least one valid partner was found (merge() returned true).
         * @return a MergeResult that gives information about all three involved states, the associated cost of merging
         * these together and which of the two partners are identical to the merged state.
         */
        @Override
        public JBCMergeResult getResult() {
            assert (this.mergeResult != null);
            assert (this.mergeResult.getPartnerState() != null);
            return this.mergeResult;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public final boolean isInstance(final State subject, final State moreGeneral) {
            return this.isInstance(subject, moreGeneral, null, null, null);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public final boolean isInstance(
            final State subject,
            final State moreGeneral,
            final AbstractVariableReference replacementRef,
            final AbstractVariableReference replacedRef)
        {
            return this.isInstance(subject, moreGeneral, replacementRef, replacedRef, null);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public final boolean isInstance(
            final State subject,
            final State moreGeneral,
            final Set<AbstractVariableReference> interestingGeneralRefs)
        {
            return this.isInstance(subject, moreGeneral, null, null, interestingGeneralRefs);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public final boolean isInstance(
            final State subject,
            final State moreGeneral,
            final AbstractVariableReference replacementRef,
            final AbstractVariableReference replacedRef,
            final Set<AbstractVariableReference> interestingGeneralRefs)
        {
            assert (this.aState == null);
            assert (moreGeneral != null);
            assert (subject != null);

            /*
             * We want to find out whether "subject" is an instance of
             * "moreGeneral". This means we must abort if information from
             * "moreGeneral" must be changed in order to be an instance of
             * "subject".
             */
            final JBCMergeResult worstResult = JBCMergeResult.FIND_INSTANCE_EDGE;

            /*
             * Construct the merged state and calculate the associated cost on
             * the way. The "other" state here is "moreGeneral", because we want
             * "subject" to be an instance of it.
             */
            final JBCMergeResult newResult =
                new JBCMergeResult(
                    moreGeneral,
                    true,
                    worstResult,
                    replacementRef,
                    replacedRef,
                    interestingGeneralRefs,
                    true);
            this.mergeResult = newResult;
            return this.computeResult(subject, moreGeneral, newResult);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean merge(final State b) {
            assert (b != null);

            /*
             * Construct the merged state and calculate the associated cost on
             * the way.
             */
            final JBCMergeResult newResult = new JBCMergeResult(b, true, this.mergeResult, this.increaseCounters);

            if (this.computeResult(this.aState, b, newResult)) {
                /*
                 * When we reach this code, we found some better merge result
                 * than before. Provide it as current best result.
                 */
                this.mergeResult = newResult;
                return true;
            }
            return false;
        }

        /**
         * Do not increase the (AbstractInterval) counters during the merge.
         */
        public void setDoNotIncreaseCounters() {
            this.increaseCounters = false;
        }
    }

    /**
     * @return the result of the merging process, including all three states and the associated cost. The result also
     * includes the information, whether A is an instance of B.
     */
    JBCMergeResult getResult();

    /**
     * @return true iff state "subject" is an instance of "moreGeneral" when only considering interesting references.
     * @param subject the state that should be an instance of the other state
     * @param moreGeneral a state which should be more general than the other state
     * @param interestingGeneralRefs the interesting references in state <code>moreGeneral</code>
     */
    boolean isInstance(State subject, State moreGeneral, Set<AbstractVariableReference> interestingGeneralRefs);

    /**
     * @return true iff state "subject" is an instance of "moreGeneral".
     * @param subject the state that should be an instance of the other state
     * @param moreGeneral a state which should be more general than the other state
     * @param replacementRef for refine reversible checks after an equality refinement, this is the replacement
     * reference (null otherwise)
     * @param replacedRef for refine reversible checks after an equality refinement, this is the replaced reference
     * (null otherwise)
     */
    boolean isInstance(
        State subject,
        State moreGeneral,
        AbstractVariableReference replacementRef,
        AbstractVariableReference replacedRef);

    /**
     * @return true iff state "subject" is an instance of "moreGeneral".
     * @param subject the state that should be an instance of the other state
     * @param moreGeneral a state which should be more general than the other state
     * @param replacementRef for refine reversible checks after an equality refinement, this is the replacement
     * reference (null otherwise)
     * @param replacedRef for refine reversible checks after an equality refinement, this is the replaced reference
     * (null otherwise)
     * @param interestingGeneralRefs the interesting references in state <code>moreGeneral</code>
     */
    boolean isInstance(
        State subject,
        State moreGeneral,
        AbstractVariableReference replacementRef,
        AbstractVariableReference replacedRef,
        Set<AbstractVariableReference> interestingGeneralRefs);

    /**
     * @return true iff state "subject" is an instance of "moreGeneral".
     * @param subject the state that should be an instance of the other state
     * @param moreGeneral a state which should be more general than the other state
     */
    boolean isInstance(State subject, State moreGeneral);

    /**
     * Try to merge the already known state A with the given state B.
     * @param b B
     * @return true iff a new (better) result was found
     */
    boolean merge(State b);
}
