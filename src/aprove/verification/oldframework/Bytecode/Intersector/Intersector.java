package aprove.verification.oldframework.Bytecode.Intersector;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.runtime.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * The framework for intersecting abstract states s, s' to obtain a new state s_i representing those states that are
 * represented by both s and s'. The general definition is taken from our RTA'11 paper, but was adapted to also handle
 * annotations.
 * @author Marc Brockschmidt
 */
public final class Intersector {

    private static Collection<FuzzyType> classAndStringFts(JBCOptions options) {
        if (options.simplifiedClassHandling()) {
            if (options.simplifiedStringHandling()) {
                return Collections.emptyList();
            } else {
                return Arrays.asList(FuzzyClassType.FT_JAVA_LANG_STRING);
            }
        } else {
            if (options.simplifiedStringHandling()) {
                return Arrays.asList(FuzzyClassType.FT_JAVA_LANG_CLASS);
            } else {
                return Arrays.asList(FuzzyClassType.FT_JAVA_LANG_CLASS, FuzzyClassType.FT_JAVA_LANG_STRING);
            }
        }
    }

    /** One of the intersected states. */
    private final State state1;
    /** The other intersected states. */
    private final State state2;
    /** The intersection result. */
    private final State targetState;
    /** The state/reference pair partition used for the intersection. */
    private final IntersectorRefPartition partition;
    /** Heap positions cache, computing these is expensive. */
    private final Map<State, HeapPositions> heapPosCache;

    private final JBCOptions options;

    /**
     * @param s1 some state
     * @param s2 some other state
     * @param p a partition of the state/reference pairs induced by <code>s1</code> and some other state.
     * @return the intersection of <code>s1</code> and the other state that was used to create <code>p</code>
     * @throws IntersectionFailException if the intersection is empty
     */
    public static State intersect(final State s1, final State s2, final IntersectorRefPartition p)
        throws IntersectionFailException
    {
        final Intersector intersector = new Intersector(s1, s2, p);
        return intersector.targetState;
    }

    /**
     * @param s1 some state
     * @param s2 some other state
     * @return the intersection of <code>s1</code> and <code>s2</code>
     * @throws IntersectionFailException if the intersection is empty
     */
    public static State intersect(final State s1, final State s2) throws IntersectionFailException {
        return Intersector.intersectAndRename(s1, s2).x;
    }

    /**
     * @param s1 some state
     * @param s2 some other state
     * @return the intersection of <code>s1</code> and <code>s2</code> and maps with the replacements from s1/s2 to the
     * resulting state
     * @throws IntersectionFailException if the intersection is empty
     */
    public static
        Triple<State, Map<AbstractVariableReference, AbstractVariableReference>, Map<AbstractVariableReference, AbstractVariableReference>>
        intersectAndRename(final State s1, final State s2) throws IntersectionFailException
    {
        final IntersectorRefPartition p = IntersectorRefPartition.fromPositionCorrespondence(s1, s2);
        final State res = Intersector.intersect(s1, s2, p);
        return new Triple<>(res, p.getRenaming(s1), p.getRenaming(s2));
    }

    /**
     * @param s1 some state
     * @param s2 some other state
     * @param p a partition of the state/reference pairs induced by <code>s1</code> and <code>s2</code>
     * @throws IntersectionFailException if the intersection is empty
     */
    private Intersector(final State s1, final State s2, final IntersectorRefPartition p)
        throws IntersectionFailException
    {
        this.state1 = s1;
        this.state2 = s2;
        this.partition = p;
        this.heapPosCache = new LinkedHashMap<>(2);
        this.options = s1.getJBCOptions();

        /*
         * The big picture:
         *  (1) Create new state as plain copy of s1, then remove all annotations.
         *  (2) For all reference equivalence classes, generate new values by intersecting their respective values and
         *      add them to the result state (this might change the equivalence classes to map more values to NULL)
         *  (3) Do the optimizations that check if the intersection should even exist (i.e., if r is on realized cycle
         *      in s1, but cannot be cyclic in s2, we fail)
         *  (4) Replace all copied references in the result by the corresponding new references.
         *  (5) Take all annotations from s1, then see if the corresponding references in s2 also have the annotation.
         *      If yes, add them to the result state.
         */
        this.targetState = s1.clone();
        final HeapAnnotations targetAnnotations = this.targetState.getHeapAnnotations();
        targetAnnotations.clear();

        for (final ImmutableSet<StateAndRef> eqClass : this.partition.getEquivalenceClasses()) {
            this.processEquivalenceClass(eqClass);
        }

        /*
         * Check every pair of references in the same equivalence class (i.e.
         * those that are combined to yield the same reference) to see if there
         * might be something that's not allowed.
         */
        final Collection<ImmutableSet<StateAndRef>> done = new LinkedHashSet<>();
        /*
         * In every iteration we may merge an equivalence class with the class of NULL, so we need to also consider
         * newly created equivalence classes.
         */
        LinkedHashSet<ImmutableSet<StateAndRef>> todo = this.partition.getEquivalenceClasses();
        Iterator<ImmutableSet<StateAndRef>> it = todo.iterator();
        while (it.hasNext()) {
            final ImmutableSet<StateAndRef> eqClass = it.next();
            if (!done.add(eqClass)) {
                continue;
            }

            //Those references that are mapped to NULL are not interesting.
            if (this.partition.getNewRefFor(eqClass).isNULLRef()) {
                continue;
            }

            for (final StateAndRef pA : eqClass) {
                for (final StateAndRef pB : eqClass) {
                    if (pA == pB) {
                        continue;
                    }
                    this.checkIfReferencesMayBeEqual(pA, pB);
                }
            }

            // there may be new eq classes (the ones already done will be skipped)
            todo = this.partition.getEquivalenceClasses();
            it = todo.iterator();
        }

        //Use the new references in the target state:
        for (final ImmutableSet<StateAndRef> eqClass : this.partition.getEquivalenceClasses()) {
            final AbstractVariableReference newRef = this.partition.getNewRefFor(eqClass);
            for (final StateAndRef pair : eqClass) {
                final State s = pair.x;
                final AbstractVariableReference ref = pair.y;
                if (s == s1 && !ref.isNULLRef()) {
                    this.targetState.replaceReferencesWithoutAnnotations(ref, newRef);
                }
            }
        }

        //Intersect annotations and store them in the target state:
        this.intersectUnaryAnnotations();
        this.intersectBinaryAnnotations();

        this.checkAndAddDefiniteReachability();
        this.checkAndAddArrayInfo();

        this.intersectConcreteStringsAndClassInstances();

        if (Globals.DEBUG_COTTO) {
            for (final AbstractVariableReference ref : this.targetState.getReferences().keySet()) {
                if (ref.isNULLRef() || !ref.pointsToReferenceType()) {
                    continue;
                }
                assert (this.targetState.getAbstractVariable(ref) != null || this.targetState
                    .getHeapAnnotations()
                    .isMaybeExisting(ref));
                assert (this.targetState.getAbstractType(ref) != null);
            }
        }
    }

    private void intersectConcreteStringsAndClassInstances() throws IntersectionFailException {
        for (Entry<AbstractVariableReference, String> e: state1.getConcreteStrings().entrySet()) {
            AbstractVariableReference ref = e.getKey();
            String val = e.getValue();
            ImmutableSet<StateAndRef> eqClass = partition.getEquivalenceClass(state1, ref);
            for (AbstractVariableReference otherRef: filterEqClassForState(eqClass, state2)) {
                String otherVal = state2.getConcreteString(otherRef);
                if (val != null && otherVal != null && !val.equals(otherVal)) {
                    throw new IntersectionFailException("references from same equivalence class point to different concrete strings");
                } else if (val != null || otherVal != null) {
                    String intersectedVal = val == null ? otherVal : val;
                    AbstractVariableReference newRef = partition.getNewRefFor(eqClass);
                    targetState.setConcreteString(newRef, intersectedVal);
                }
            }
        }
        for (Entry<AbstractVariableReference, FuzzyType> e: state1.getClassInstances().entrySet()) {
            AbstractVariableReference ref = e.getKey();
            FuzzyType val = e.getValue();
            ImmutableSet<StateAndRef> eqClass = partition.getEquivalenceClass(state1, ref);
            for (AbstractVariableReference otherRef: filterEqClassForState(eqClass, state2)) {
                FuzzyType otherVal = state2.getClassInstance(otherRef);
                if (val != null && otherVal != null && !val.equals(otherVal)) {
                    throw new IntersectionFailException("references from same equivalence class point to different class insetances");
                } else if (val != null || otherVal != null) {
                    FuzzyType intersectedVal = val == null ? otherVal : val;
                    AbstractVariableReference newRef = partition.getNewRefFor(eqClass);
                    targetState.setClassInstance(newRef, intersectedVal);
                }
            }
        }
    }

    /**
     * Add the union of the array information to the intersected state otherwise.
     * @throws IntersectionFailException if the array information from one state is impossible in the other state.
     */
    private void checkAndAddArrayInfo() throws IntersectionFailException {
        final ArrayInfo targetArrayInfo = this.targetState.getHeapAnnotations().getArrayInfo();

        final Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>> fromStateOne =
            this.collectAndCheckArrayInfo(true);
        final Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>> fromStateTwo =
            this.collectAndCheckArrayInfo(false);

        final Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>> addMe =
            new LinkedHashSet<>();
        addMe.addAll(fromStateOne);
        addMe.addAll(fromStateTwo);
        for (final Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference> triple : addMe)
        {
            targetArrayInfo.add(triple.x, triple.y, triple.z);
        }
    }

    /**
     * Check that all information from the given state also is possible in the other state.
     * @param stateOne iff true, consider information from this.state1.
     * @return the information from the given state with references from the target state
     * @throws IntersectionFailException if the array information from one state is impossible in the other state.
     */
    private
        Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>>
        collectAndCheckArrayInfo(final boolean stateOne) throws IntersectionFailException
    {
        final Collection<Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference>> res =
            new LinkedHashSet<>();
        State state;
        State otherState;
        if (stateOne) {
            state = this.state1;
            otherState = this.state2;
        } else {
            state = this.state2;
            otherState = this.state1;
        }

        final ArrayInfo arrayInfo = state.getHeapAnnotations().getArrayInfo();

        for (final Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference> triple : arrayInfo
            .getTriples())
        {
            final AbstractVariableReference arrayRefTarget = this.getNewRefName(state, triple.x);
            final AbstractVariableReference indexRefTarget = this.getNewRefName(state, triple.y);
            final AbstractVariableReference contentRefTarget = this.getNewRefName(state, triple.z);

            final Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference> tripleTarget =
                new Triple<>(arrayRefTarget, indexRefTarget, contentRefTarget);

            for (final AbstractVariableReference arrayOther : Intersector.filterEqClassForState(
                this.partition.getEquivalenceClass(state, triple.x),
                otherState))
            {
                for (final AbstractVariableReference indexOther : Intersector.filterEqClassForState(
                    this.partition.getEquivalenceClass(state, triple.y),
                    otherState))
                {
                    for (final AbstractVariableReference contentOther : Intersector.filterEqClassForState(
                        this.partition.getEquivalenceClass(state, triple.z),
                        otherState))
                    {
                        final Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference> tripleOther =
                            new Triple<>(arrayOther, indexOther, contentOther);
                        if (this.mayBeRepresented(tripleOther, otherState)) {
                            res.add(tripleTarget);
                        } else {
                            final String msg =
                                triple.x + "[" + triple.y + "] = " + triple.z + " must hold in the other state";
                            throw new IntersectionFailException(msg);
                        }
                    }
                }
            }
        }

        return res;
    }

    /**
     * Check if array[index] = content may hold in state.
     * @param triple a triple of references a, b, c indicating a[b] = c holds in state
     * @param state a state where we want to check if the information from the triple holds
     * @return false only if we know that array[index] = content does not hold in the given state
     */
    public boolean mayBeRepresented(
        final Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference> triple,
        final State state)
    {

        final AbstractVariableReference arrayRef = triple.x;
        final AbstractVariableReference indexRef = triple.y;
        final AbstractVariableReference contentRef = triple.z;
        if (arrayRef.isNULLRef()) {
            return false;
        }

        // maybe we can just have a look at the array?
        final AbstractVariable var = state.getAbstractVariable(arrayRef);
        if (var instanceof ConcreteArray) {
            final ConcreteArray array = (ConcreteArray) var;

            if (indexRef.pointsToConstantInt()) {
                final AbstractVariable indexVar = state.getAbstractVariable(indexRef);
                final AbstractInt aInt = (AbstractInt) indexVar;
                final AbstractVariableReference contentInConcrete = array.getData()[aInt.getLiteral().intValue()];
                if (!this.mayBeEqual(contentInConcrete, contentRef, state)) {
                    return false;
                }
            } else {
                // just check all values
                for (final AbstractVariableReference inArray : array.getData()) {
                    if (!this.mayBeEqual(inArray, contentRef, state)) {
                        return false;
                    }
                }
            }
        } else {
            // we know that array joins content holds
            if (!state.getHeapAnnotations().getJoiningStructures().areJoining(arrayRef, contentRef)) {
                return false;
            }
        }

        return true;
    }

    /**
     * @param refA a reference
     * @param refB a reference
     * @param state a state
     * @return false only if we know that refA = refB does not hold in the given state
     */
    private boolean mayBeEqual(
        final AbstractVariableReference refA,
        final AbstractVariableReference refB,
        final State state)
    {
        final AbstractVariableReference targetA = this.getNewRefName(state, refA);
        final AbstractVariableReference targetB = this.getNewRefName(state, refB);
        if (targetA.equals(targetB)) {
            return true;
        }
        if (targetA.pointsToAnyIntegerType() && targetB.pointsToAnyIntegerType()) {
            final JBCIntegerRelation integerRelation = new JBCIntegerRelation(refA, IntegerRelationType.NE, refB);
            if (state.checkIntegerRelation(integerRelation)) {
                // we know that the content differs
                return false;
            }
        } else if (refA.pointsToReferenceType() && refB.pointsToReferenceType()) {
            if (refA.isNULLRef()) {
                if (!state.getHeapAnnotations().isMaybeExisting(refB)) {
                    return false;
                }
            } else if (refB.isNULLRef()) {
                if (!state.getHeapAnnotations().isMaybeExisting(refA)) {
                    return false;
                }
            } else if (!state.getHeapAnnotations().getEqualityGraph().areMarkedAsPossiblyEqual(refA, refB)) {
                return false;
            }
        } else {
            // type difference
            return false;
        }
        return true;
    }

    /**
     * @throws IntersectionFailException
     */
    private void checkAndAddDefiniteReachability() throws IntersectionFailException {
        final HeapPositions heapPosOne = this.getHeapPosFor(this.state1);
        final HeapPositions heapPosTwo = this.getHeapPosFor(this.state2);
        final HeapPositions heapPosTarget = this.getHeapPosFor(this.targetState);

        // the connections we found in the first state must also exist (somehow) in the second state and vice versa
        DefiniteReachabilities.checkDefiniteReaches(heapPosTwo, heapPosOne);
        DefiniteReachabilities.checkDefiniteReaches(heapPosOne, heapPosTwo);

        // find connections that exist in the first state
        final Set<DefiniteReachabilityAnnotation> fromOne =
            DefiniteReachabilityAnnotation.getCommonConnections(heapPosOne, heapPosTarget);

        // find connections that exist in the second state
        final Set<DefiniteReachabilityAnnotation> fromTwo =
            DefiniteReachabilityAnnotation.getCommonConnections(heapPosTwo, heapPosTarget);

        // everything is OK, add all annotations to the target state
        final Collection<DefiniteReachabilityAnnotation> union = new LinkedHashSet<>(fromOne);
        union.addAll(fromTwo);

        for (final DefiniteReachabilityAnnotation defReach : union) {
            final AbstractVariableReference f = defReach.getFrom();
            final AbstractVariableReference t = defReach.getTo();
            if (this.targetState.getHeapAnnotations().isMaybeExisting(t)) {
                // useless
                continue;
            }
            final boolean atLeastOneStep = defReach.isAtLeastOneStep();
            if (Reachability.followFields(f, defReach.getFields(), t, atLeastOneStep, this.targetState) == t) {
                // adding this is useless
                continue;
            }

            assert (!this.targetState.getHeapAnnotations().isMaybeExisting(defReach.getTo()));

            this.targetState.getHeapAnnotations().getDefiniteReachabilities().add(defReach);
        }
        DefiniteReachabilities.generateAdditionalAnnotations(heapPosTarget);
    }

    /**
     * Checks if two reference/state pairs may be mapped to the same value or not by checking if (realized) structural
     * information such as reachability or cyclicity on one side is represented on the other side.
     * @param pA some state/reference pair
     * @param pB some state/reference pair that should be equivalent to to pA
     * @throws IntersectionFailException if the intersection is empty
     */
    private void checkIfReferencesMayBeEqual(final StateAndRef pA, final StateAndRef pB)
        throws IntersectionFailException
    {
        assert (this.partition.areEquivalent(pA, pB)) : "Wrong arguments in call to checkCorrespondenceOfSuccessors";

        if (!pA.y.pointsToReferenceType() && !pB.y.pointsToReferenceType()) {
            return;
        }

        this.checkCorrespondenceOfSuccessors(pA, pB);
        this.checkNonTreenessOfSuccessors(pA, pB);
    }

    /**
     * Checks for a reference pair if the successor of the two references are corresponding to each other. If not, we
     * have an empty intersection.
     * @param pA some state/reference pair
     * @param pB some state/reference pair that should be equivalent to to pA
     * @throws IntersectionFailException if the intersection is empty
     */
    private void checkCorrespondenceOfSuccessors(final StateAndRef pA, final StateAndRef pB)
        throws IntersectionFailException
    {
        final State stateA = pA.x;
        final HeapPositions heapPosA = this.getHeapPosFor(stateA);
        final AbstractVariableReference refA = pA.y;
        final State stateB = pB.x;
        final HeapPositions heapPosB = this.getHeapPosFor(stateB);
        final AbstractVariableReference refB = pB.y;

        /*
         * For every reachable reference reachedRefA from refA using realized connections, we need to be able to reach a
         * corresponding reference reachedRefB from refB (where reachedRefA and reachedRefB are in the same equivalence
         * class) with either the same realized path or some realized path and then a possible equality/joins
         * annotation. If this connection is missing, the intersection fails. As an example, for refA.f = x we need
         * refB \rightsquigarrow x' with x ~ x'.
         *
         * Note however, that we do not need to check if for
         *  refA.f -><- abstractlyReachedRef
         * there is a correspondence in stateB - these are never the reason for a failed intersection (as they are
         * optional connections!) and the intersection of annotations is done at another time.
         */
        final Collection<AbstractVariableReference> reachableRefsA;
        if (refA.isNULLRef()) {
            reachableRefsA = Collections.emptySet();
        } else {
            reachableRefsA = Reachability.getReachableRefs(refA, false, stateA);
        }
        final Collection<AbstractVariableReference> reachableRefsB;
        if (refB.isNULLRef()) {
            reachableRefsB = Collections.emptySet();
        } else {
            reachableRefsB = Reachability.getReachableRefs(refB, false, stateB);
            reachableRefsB.add(refB);
        }

        final Collection<AbstractVariableReference> validReferencesB = heapPosB.getReferencesAndPositions().keySet();

        refAReachables: for (final AbstractVariableReference reachedRefA : reachableRefsA) {
            final ImmutableSet<StateAndRef> eqClassReachedA = this.partition.getEquivalenceClass(stateA, reachedRefA);
            final Set<AbstractVariableReference> reachedRefAEquivsInB = Intersector.filterEqClassForState(eqClassReachedA, stateB);

            /*
             * There is no corresponding reference in stateB, so we cannot check
             * for reachability.
             */
            if (reachedRefAEquivsInB.isEmpty()) {
                continue refAReachables;
            }

            for (final AbstractVariableReference reachedRefAEquivInB : reachedRefAEquivsInB) {
                if (reachableRefsB.contains(reachedRefAEquivInB)) {
                    continue refAReachables;
                }
            }

            //No concrete connection. Guess we have to find an abstract one.
            final Collection<Set<HeapEdge>> collectionOfNeededConnections =
                heapPosA.getNeededConnections(refA, reachedRefA, true);
            boolean missesConnection = false;
            for (final Set<HeapEdge> neededConnection : collectionOfNeededConnections) {
                if (!Intersector.hasConnectionFromRefToRefEqClass(
                    refB,
                    reachedRefAEquivsInB,
                    heapPosB,
                    neededConnection,
                    reachableRefsB,
                    validReferencesB))
                {
                    missesConnection = true;
                    break;
                }
            }

            /*
             * We are missing a connection. If the missing reference is possibly
             * existing, we need to merge it with the equivalence class for
             * null. Otherwise, we fail:
             */
            if (missesConnection) {
                /*
                 * For String and Class objects, we do special stuff in
                 * non-competition mode and the checks won't work:
                 */
                final AbstractType reachedRefAType = stateA.getAbstractType(reachedRefA);
                final AbstractType classStringTypeIntersection;
                if (classAndStringFts(options).isEmpty()) {
                    classStringTypeIntersection = null;
                } else {
                    classStringTypeIntersection = AbstractType.intersection(stateA.getClassPath(),
                            options,
                            reachedRefAType,
                            new AbstractType(stateA.getClassPath(), options, classAndStringFts(options)));
                }

                if (classStringTypeIntersection == null) {
                    for (final StateAndRef p : eqClassReachedA) {
                        if (!p.x.getHeapAnnotations().isMaybeExisting(p.y) && !p.y.isNULLRef()) {
                            String msg =
                                "Connection between " + refA + " and " + reachedRefA + " missing in other state!";
                            msg += " (" + refB + " to all of " + reachedRefAEquivsInB + ")";
                            throw new IntersectionFailException(msg);
                        }
                    }
                    //All are allowed to be null, so merge the class to the NULL one:

                    final AbstractVariableReference newRefName = this.partition.getNewRefFor(eqClassReachedA);
                    if (newRefName != null && !newRefName.isNULLRef()) {
                        this.targetState.replaceReference(newRefName, AbstractVariableReference.NULLREF);
                    }

                    this.partition.mergeWithNullEquivalenceClass(eqClassReachedA);
                } else {
                    final AbstractVariableReference newRefName = this.partition.getNewRefFor(eqClassReachedA);
                    if (newRefName != null && !newRefName.isNULLRef()) {
                        this.targetState.setAbstractType(newRefName, classStringTypeIntersection);
                    }
                }
            }
        }
    }

    /**
     * Checks for a reference pair if the non-tree shapes behind each of the two references are allowed by the other. If
     * not, we have an empty intersection.
     * @param pA some state/reference pair
     * @param pB some state/reference pair that should be equivalent to to pA
     * @throws IntersectionFailException if the intersection is empty
     */
    private void checkNonTreenessOfSuccessors(final StateAndRef pA, final StateAndRef pB)
        throws IntersectionFailException
    {
        final State stateA = pA.x;
        final HeapPositions heapPosA = this.getHeapPosFor(stateA);
        final AbstractVariableReference refA = pA.y;
        final State stateB = pB.x;
        final HeapAnnotations heapAnnotationsB = stateB.getHeapAnnotations();
        final AbstractVariableReference refB = pB.y;

        /*
         * These optimizations only work if there are no fields going out from
         * refB (but that's not enough, because if there is a concrete successor
         * succB of refB that has the problem, we will notice it when we
         * consider succB paired with its corresponding reference):
         */
        final AbstractVariable valB = stateB.getAbstractVariable(refB);
        if (valB != null && !refB.isNULLRef()) {
            if (valB instanceof ConcreteArray) {
                return;
            } else if (valB instanceof ConcreteInstance) {
                if (!((ConcreteInstance) valB).isOnlyRealizedUpToJLO()) {
                    return;
                }
            }
        }

        if (!heapAnnotationsB.isPossiblyNonTree(refB)) {
            /*
             * Is there a realized tree-shape visible from refA, that is not
             * allowed because refB does not have the non-tree annotation?
             */
            if (Intersector.hasRealizedNonTree(refA, heapPosA)) {
                throw new IntersectionFailException("(non-tree) " + refA + " = " + refB);
            }
        }

        // cyclic
        final CyclicStructures cyclicStructuresB = heapAnnotationsB.getCyclicStructures();
        if (cyclicStructuresB.isCyclic(refB)) {
            final ImmutableSet<HeapEdge> neededEdgesForRefBCycles = cyclicStructuresB.getNeededEdgesOf(refB);
            /*
             * There may be realized cycles behind refA that do not conform to
             * the information provided by refB. If we can find such a cycle,
             * we have a failed intersection.
             *
             * Check all realized cycles in stateA.
             * (The cycles introduced by this intersection will be checked
             *  afterwards.)
             */
            for (final Collection<HeapEdge> cycleEdges : Intersector.getRealizedCycles(refA, heapPosA)) {
                if (!cycleEdges.containsAll(neededEdgesForRefBCycles)) {
                    /*
                     * There is a realized cycle reachable from refA to refA,
                     * involving the edges in the variable "cycleEdges".
                     * However, the cyclic annotation for replacedRef
                     * does not represent this cycle.
                     */
                    throw new IntersectionFailException("(edges on cycle) " + refA + " = " + refB);
                }
            }
        } else {
            if (!Intersector.getRealizedCycles(refA, heapPosA).isEmpty()) {
                throw new IntersectionFailException("(cyclic vs acyclic) " + refA + " = " + refB);
            }
        }
    }

    /**
     * @param refB some reference
     * @param refBsToReach other references of which at least one should be reached.
     * @param heapPosB the heap positions of the state in which <code>refB</code> lives.
     * @param neededConnection the set of edges that need to be allowed by the connection from <code>refB</code> to
     * <code>refBsToReach</code>
     * @param refBReachableRefs the references concretely reachable from <code>refB</code>
     * @param validReferencesB when handling a method return, the states may contain a lot of garbage. This set contains
     * the references that are valid in the state of heapPosB.
     * @return true iff there is a connection from <code>refB</code> to one of the references from
     * <code>refBsToReach</code> allowing the edges from <code>neededConnection</code>.
     */
    private static boolean hasConnectionFromRefToRefEqClass(
        final AbstractVariableReference refB,
        final Set<AbstractVariableReference> refBsToReach,
        final HeapPositions heapPosB,
        final Set<HeapEdge> neededConnection,
        final Collection<AbstractVariableReference> refBReachableRefs,
        final Collection<AbstractVariableReference> validReferencesB)
    {
        final State stateB = heapPosB.getState();
        final EqualityGraph eqGraphB = stateB.getHeapAnnotations().getEqualityGraph();
        final JoiningStructures joiningStructuresB = stateB.getHeapAnnotations().getJoiningStructures();

        for (final AbstractVariableReference reachedRefAEquivInB : refBsToReach) {
            for (final AbstractVariableReference reachedRefAEquivInBEqPartner : eqGraphB
                .getPartners(reachedRefAEquivInB))
            {
                if (!validReferencesB.contains(reachedRefAEquivInBEqPartner)) {
                    continue;
                }
                final Collection<Set<HeapEdge>> collectionOfExistingConnection =
                    heapPosB.getNeededConnections(refB, reachedRefAEquivInBEqPartner, true);
                if (collectionOfExistingConnection.contains(neededConnection)) {
                    return true;
                }
            }

            for (final AbstractVariableReference partner : joiningStructuresB
                .getReferencesWithPartner(reachedRefAEquivInB))
            {
                if (!validReferencesB.contains(partner)) {
                    continue;
                }
                if (refBReachableRefs.contains(partner)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * @param eqClass some equivalence class
     * @throws IntersectionFailException if the intersection is empty
     */
    private void processEquivalenceClass(final ImmutableSet<StateAndRef> eqClass) throws IntersectionFailException {
        final Iterator<StateAndRef> eqClassIter = eqClass.iterator();
        final StateAndRef firstP = eqClassIter.next();
        if (!firstP.y.pointsToReferenceType()) {
            this.processPrimitiveEquivalenceClass(eqClass);
        } else {
            this.processReferenceEquivalenceClass(eqClass);
        }
    }

    /**
     * @param eqClass some equivalence class
     * @throws IntersectionFailException if the intersection is empty
     */
    private void processPrimitiveEquivalenceClass(final ImmutableSet<StateAndRef> eqClass)
        throws IntersectionFailException
    {
        if (Globals.DEBUG_MARC) {
            for (final StateAndRef p : eqClass) {
                assert (!p.y.pointsToReferenceType()) : "Type error in intersection: Intersecting primitive and non-primitive values!";
            }
        }

        final Iterator<StateAndRef> eqClassIter = eqClass.iterator();
        final StateAndRef firstP = eqClassIter.next();
        AbstractNumber resVal = (AbstractNumber) firstP.x.getAbstractVariable(firstP.y);
        while (eqClassIter.hasNext()) {
            final StateAndRef curP = eqClassIter.next();
            final AbstractNumber curVal = (AbstractNumber) curP.x.getAbstractVariable(curP.y);
            resVal = resVal.intersect(curVal);
        }

        final AbstractVariableReference newRefName = this.partition.getNewRefFor(eqClass);
        if (resVal.isLiteral() && !newRefName.pointsToConstant()) {
            final AbstractVariableReference veryNewRefName =
                AbstractVariableReference.create(resVal, newRefName.getPrimitiveType());
            this.partition.replaceRefFor(eqClass, veryNewRefName);
            this.targetState.replaceReference(newRefName, veryNewRefName);
            this.targetState.addAbstractVariable(veryNewRefName, resVal);
        } else {
            this.targetState.addAbstractVariable(newRefName, resVal);
        }
    }

    /**
     * @param eqClass some equivalence class
     * @throws IntersectionFailException if the intersection is empty
     */
    private void processReferenceEquivalenceClass(final ImmutableSet<StateAndRef> eqClass)
        throws IntersectionFailException
    {
        if (Globals.DEBUG_MARC) {
            for (final StateAndRef p : eqClass) {
                assert (p.y.pointsToReferenceType()) : "Type error in intersection: Intersecting primitive and non-primitive values!";
            }
        }

        /*
         * First, separate the references into sets corresponding to the two
         * states. On the way, collect type and nullness information.
         */
        final CollectionMap<State, AbstractVariableReference> refsPerState = new CollectionMap<>();
        final List<AbstractType> types = new LinkedList<>();
        final List<AbstractType> reachableTypes = new LinkedList<>();
        boolean isNull = false;
        ClassPath cPath = null;
        for (final StateAndRef p : eqClass) {
            refsPerState.add(p.x, p.y);
            cPath = p.x.getClassPath();
            if (p.y.isNULLRef()) {
                isNull = true;
            } else {
                final AbstractType reachTypes = p.x.getHeapAnnotations().getReachableTypes(p.y);
                reachableTypes.add(reachTypes);
                types.add(p.x.getHeapAnnotations().getAbstractType(p.y));
            }
        }

        /*
         * Divide the references up into two sets, one per state. Then check
         * if references from one state are missing a possible equality.
         */
        final Iterator<Entry<State, Collection<AbstractVariableReference>>> it = refsPerState.entrySet().iterator();
        final Entry<State, Collection<AbstractVariableReference>> pOne = it.next();
        final State stateOne = pOne.getKey();
        final Collection<AbstractVariableReference> refsStateOne = pOne.getValue();
        final State stateTwo;
        final Collection<AbstractVariableReference> refsStateTwo;
        if (it.hasNext()) {
            final Entry<State, Collection<AbstractVariableReference>> pTwo = it.next();
            stateTwo = pTwo.getKey();
            refsStateTwo = pTwo.getValue();
        } else {
            refsStateTwo = Collections.emptySet();
            stateTwo = null;
        }
        assert (!it.hasNext()) : "Looks like we are intersecting three states!";

        boolean areEqualOne = true;
        boolean areEqualTwo = true;
        if (!isNull) {
            areEqualOne = Intersector.areAllPossiblyEqual(stateOne, refsStateOne);
            isNull |= !areEqualOne;
        }
        if (!isNull) {
            areEqualTwo = Intersector.areAllPossiblyEqual(stateTwo, refsStateTwo);
            isNull |= !areEqualTwo;
        }

        // Compute the type intersection, choose null if the result is empty.
        final AbstractType resType;
        if (!isNull) {
            resType = AbstractType.intersection(cPath, options, types);

            //If the type intersection is empty, try setting the value to NULL:
            if (resType == null) {
                isNull = true;
            }
        } else {
            resType = null;
        }

        final AbstractType resReachableTypes;
        if (!isNull && !reachableTypes.isEmpty()) {
            resReachableTypes = AbstractType.intersection(cPath, options, reachableTypes);
        } else {
            resReachableTypes = null;
        }

        // Now create the actual references and values:
        if (isNull) {
            //Check if all partners allow nullness:
            for (final StateAndRef p : eqClass) {
                if (!p.y.isNULLRef() && !p.x.getHeapAnnotations().isMaybeExisting(p.y)) {
                    String msg;
                    if (!areEqualOne) {
                        msg = "The references " + refsStateOne + " must be equal (or all null)!";
                    } else if (!areEqualTwo) {
                        msg = "The references " + refsStateTwo + " must be equal (or all null)!";
                    } else {
                        msg = p.y + " cannot be intersected with null!";
                    }
                    throw new IntersectionFailException(msg);
                }
            }
            final AbstractVariableReference newRefName = this.partition.getNewRefFor(eqClass);
            if (newRefName != null && !newRefName.isNULLRef()) {
                this.targetState.replaceReference(newRefName, AbstractVariableReference.NULLREF);
            }
            this.partition.mergeWithNullEquivalenceClass(eqClass);
            if (stateTwo != null) {
                this.partition.mergeWithNullEquivalenceClass(eqClass);
            }
        } else {
            final AbstractVariable newVal = this.intersectReferenceEqClassValues(eqClass);
            final AbstractVariableReference newRefName = this.partition.getNewRefFor(eqClass);
            this.targetState.getHeapAnnotations().setAbstractType(newRefName, resType);
            if (resReachableTypes != null) {
                this.targetState.getHeapAnnotations().setReachableTypes(newRefName, resReachableTypes);
            }
            if (newVal != null) {
                this.targetState.removeAbstractVariable(newRefName);
                this.targetState.addAbstractVariable(newRefName, newVal);
            }
        }
    }

    /**
     * Intersect the unary annotations of state1 and state2 (i.e., information about possibly existing instances and
     * possibly non-tree/cyclic structures) and put the result into targetState.
     */
    private void intersectUnaryAnnotations() {
        this.intersectMaybeExisting(this.state1);
        this.intersectMaybeExisting(this.state2);
        this.intersectPossiblyNonTree(this.state1);
        this.intersectPossiblyNonTree(this.state2);
        this.intersectCyclicStructures(this.state1);
        this.intersectCyclicStructures(this.state2);
    }

    /**
     * Intersect the information about possibly existing instances of state1 and state2 and put the result into
     * targetState.
     * @param s one of the intersected states.
     */
    private void intersectMaybeExisting(final State s) {
        final Set<AbstractVariableReference> maybeExistingInput = s.getHeapAnnotations().getMaybeExistingInstances();
        final Set<AbstractVariableReference> targetMaybeExisting =
            this.targetState.getHeapAnnotations().getMaybeExistingInstances();

        nextRef: for (final AbstractVariableReference ref : maybeExistingInput) {
            final ImmutableSet<StateAndRef> equivReferences = this.partition.getEquivalenceClass(s, ref);
            if (equivReferences == null) {
                //This happens if the state wasn't GC'ed yet.
                continue;
            }

            final AbstractVariableReference newRef = this.partition.getNewRefFor(s, ref);
            assert (newRef != null);

            for (final StateAndRef equivP : equivReferences) {
                final Set<AbstractVariableReference> maybeExistingOther =
                    equivP.x.getHeapAnnotations().getMaybeExistingInstances();
                final AbstractVariableReference equivR = equivP.y;
                if (!maybeExistingOther.contains(equivR)) {
                    continue nextRef;
                }
            }
            targetMaybeExisting.add(newRef);
        }
    }

    /**
     * Intersect the information about possibly non-tree structures of state1 and state2 and put the result into
     * targetState.
     * @param s one of the intersected states.
     */
    private void intersectPossiblyNonTree(final State s) {
        final Set<AbstractVariableReference> possiblyNonTreeInput = s.getHeapAnnotations().getPossiblyNonTreeRefs();
        final Set<AbstractVariableReference> targetPossiblyNonTree =
            this.targetState.getHeapAnnotations().getPossiblyNonTreeRefs();

        nextRef: for (final AbstractVariableReference ref : possiblyNonTreeInput) {
            final ImmutableSet<StateAndRef> equivReferences = this.partition.getEquivalenceClass(s, ref);
            if (equivReferences == null) {
                continue;
            }
            for (final StateAndRef equivP : equivReferences) {
                final Set<AbstractVariableReference> possiblyNonTreeOther =
                    equivP.x.getHeapAnnotations().getPossiblyNonTreeRefs();
                final AbstractVariableReference equivR = equivP.y;
                if (!possiblyNonTreeOther.contains(equivR)) {
                    continue nextRef;
                }
            }
            final AbstractVariableReference newRef = this.partition.getNewRefFor(s, ref);
            targetPossiblyNonTree.add(newRef);
        }
    }

    /**
     * Intersect the information about possibly cyclic structures of state1 and state2 and put the result into
     * targetState.
     * @param s one of the intersected states.
     */
    private void intersectCyclicStructures(final State s) {
        final CyclicStructures cyclicStructuresInput = s.getHeapAnnotations().getCyclicStructures();
        final CyclicStructures targetCyclicStructures = this.targetState.getHeapAnnotations().getCyclicStructures();

        nextRef: for (final AbstractVariableReference r : cyclicStructuresInput.getCyclicRefs()) {
            final Set<HeapEdge> neededEdges = new LinkedHashSet<>(cyclicStructuresInput.getNeededEdgesOf(r));

            final ImmutableSet<StateAndRef> equivReferences = this.partition.getEquivalenceClass(s, r);
            if (equivReferences == null) {
                continue;
            }
            for (final StateAndRef equivP : equivReferences) {
                final CyclicStructures otherPossiblyCyclicStructures =
                    equivP.x.getHeapAnnotations().getCyclicStructures();
                final AbstractVariableReference equivR = equivP.y;
                if (!otherPossiblyCyclicStructures.isCyclic(equivR)) {
                    continue nextRef;
                }
                neededEdges.addAll(otherPossiblyCyclicStructures.getNeededEdgesOf(equivR));
            }
            final AbstractVariableReference newRef = this.partition.getNewRefFor(s, r);
            targetCyclicStructures.add(newRef, neededEdges);
        }
    }

    /**
     * Intersect the binary annotations of state1 and state2 (i.e., possible equalities and joins annotations) and put
     * the result into targetState.
     */
    private void intersectBinaryAnnotations() {
        /*
         * Binary annotation R:
         *  If we have (rL,rR) \in R in state1:
         *   \forall (s,rLP) \in eqClass(rL):
         *     \exists rRP \in filter(s, eqClass(rR)):
         *       (rLP, rRP) \in R in s
         *   \forall (s,rRP) \in eqClass(rR):
         *     \exists rLP \in filter(s, eqClass(rL)):
         *       (rLP, rRP) \in R in s
         * THEN the annotation (newName(rL),newName(rR)) needs to be created in
         * the target.
         *
         * The same also needs to be done for state2. If there is some
         * annotation rL o rR where one of the two references does not have any
         * corresponding reference in the other state (e.g. due to refinement),
         * this annotation also must exist in the target state.
         */
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> addEquality =
            new LinkedHashSet<>();
        addEquality.addAll(this.intersectPossibleEqualities(this.state1));
        addEquality.addAll(this.intersectPossibleEqualities(this.state2));

        final EqualityGraph eqGraph = this.targetState.getHeapAnnotations().getEqualityGraph();

        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : addEquality) {
            eqGraph.addPossibleEquality(this.targetState, pair.x, pair.y);
        }

        this.intersectJoiningStructures(this.state1);
        this.intersectJoiningStructures(this.state2);
    }

    /**
     * Intersect the possible equalities of state1 and state2
     * @return the pairs that need =?= in the target state.
     * @param state the state from wich the annotations are taken and checked
     */
    private Collection<Pair<AbstractVariableReference, AbstractVariableReference>> intersectPossibleEqualities(
        final State state)
    {
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> result = new LinkedHashSet<>();
        //Intersection structure explained in intersectBinaryAnnotations.
        final EqualityGraph eqGraph = state.getHeapAnnotations().getEqualityGraph();
        for (final AbstractVariableReference rL : eqGraph.getReferences()) {
            nextEq: for (final AbstractVariableReference rR : eqGraph.getPartners(rL)) {
                if (rL.compareTo(rR) > 0) {
                    continue;
                }
                final ImmutableSet<StateAndRef> rLPartners = this.partition.getEquivalenceClass(state, rL);
                final ImmutableSet<StateAndRef> rRPartners = this.partition.getEquivalenceClass(state, rR);

                if (rLPartners == null) {
                    continue;
                }
                if (rRPartners == null) {
                    continue;
                }
                for (final StateAndRef p : rLPartners) {
                    final State s = p.x;
                    final EqualityGraph eqS = s.getHeapAnnotations().getEqualityGraph();
                    final AbstractVariableReference rLP = p.y;

                    boolean foundPartnerWithoutAnnotation = false;
                    final Collection<AbstractVariableReference> rRPartnersInS = Intersector.filterEqClassForState(rRPartners, s);
                    for (final AbstractVariableReference rRP : rRPartnersInS) {
                        if (!eqS.areMarkedAsPossiblyEqual(rLP, rRP)) {
                            foundPartnerWithoutAnnotation = true;
                            break;
                        }
                    }
                    if (foundPartnerWithoutAnnotation) {
                        continue nextEq;
                    }
                }

                for (final StateAndRef p : rRPartners) {
                    final State s = p.x;
                    final EqualityGraph eqS = s.getHeapAnnotations().getEqualityGraph();
                    final AbstractVariableReference rRP = p.y;

                    boolean foundPartnerWithoutAnnotation = false;
                    final Collection<AbstractVariableReference> rLPartnersInS = Intersector.filterEqClassForState(rLPartners, s);
                    for (final AbstractVariableReference rLP : rLPartnersInS) {
                        if (!eqS.areMarkedAsPossiblyEqual(rLP, rRP)) {
                            foundPartnerWithoutAnnotation = true;
                            break;
                        }
                    }
                    if (foundPartnerWithoutAnnotation) {
                        continue nextEq;
                    }
                }

                result.add(new Pair<>(this.partition.getNewRefFor(state, rL), this.partition.getNewRefFor(state, rR)));
            }
        }

        return result;
    }

    /**
     * Intersect the joins annotations of state1 and state2 and put the result into targetState.
     * @param state the state from wich the annotations are taken and checked
     */
    private void intersectJoiningStructures(final State state) {
        //Intersection structure explained in intersectBinaryAnnotations.
        final JoiningStructures joins = state.getHeapAnnotations().getJoiningStructures();
        final JoiningStructures joinsTarget = this.targetState.getHeapAnnotations().getJoiningStructures();
        nextJoins: for (final TwoRefs twoRefs : joins.getJoinsAnnotations()) {
            final AbstractVariableReference rL = twoRefs.getRefOne();
            final ImmutableSet<StateAndRef> rLPartners = this.partition.getEquivalenceClass(state, rL);
            if (rLPartners == null) {
                continue;
            }

            final AbstractVariableReference rR = twoRefs.getRefTwo();
            final ImmutableSet<StateAndRef> rRPartners = this.partition.getEquivalenceClass(state, rR);
            if (rRPartners == null) {
                continue;
            }

            for (final StateAndRef p : rLPartners) {
                final State s = p.x;
                final JoiningStructures joinsS = s.getHeapAnnotations().getJoiningStructures();
                final AbstractVariableReference rLP = p.y;

                final Collection<AbstractVariableReference> rRPartnersInS = Intersector.filterEqClassForState(rRPartners, s);
                for (final AbstractVariableReference rRP : rRPartnersInS) {
                    if (joinsS.areJoining(rRP, rLP)) {
                        continue;
                    }
                    // found partner without annotation
                    continue nextJoins;
                }
            }

            // all partners have the annotation, also add it in the intersection
            joinsTarget.add(this.partition.getNewRefFor(state, rL), this.partition.getNewRefFor(state, rR));
        }
    }

    /**
     * @param eqClass some equivalence class of state/reference pairs
     * @param state some state
     * @return collection of references that occur in <code>eqClass</code> and are from <code>state</code>.
     */
    private static Set<AbstractVariableReference> filterEqClassForState(
        final ImmutableSet<StateAndRef> eqClass,
        final State state)
    {
        final LinkedHashSet<AbstractVariableReference> res = new LinkedHashSet<>();
        if (eqClass == null) {
            return res;
        }
        for (final StateAndRef p : eqClass) {
            if (p.x == state) {
                res.add(p.y);
            }
        }
        return res;
    }

    /**
     * @param eqClass some equivalence class of state/reference pair
     * @return a new value corresponding to the intersection of values in this equivalence class.
     * @throws IntersectionFailException if intersection failed
     */
    private AbstractVariable intersectReferenceEqClassValues(final ImmutableSet<StateAndRef> eqClass)
        throws IntersectionFailException
    {
        final Iterator<StateAndRef> it = eqClass.iterator();
        AbstractVariable newVal = null;

        /*
         * Do it once to also do the renaming of contained references if the
         * reference is alone in its equivalence class:
         */
        while (newVal == null && it.hasNext()) {
            final StateAndRef currentPair = it.next();
            newVal = currentPair.x.getAbstractVariable(currentPair.y);
            if (newVal != null) {
                newVal =
                    this.intersectReferenceValuePair(
                        currentPair.x,
                        currentPair.y,
                        newVal,
                        currentPair.x,
                        currentPair.y,
                        newVal);
            }
        }

        while (it.hasNext()) {
            final StateAndRef curP = it.next();
            newVal =
                this.intersectReferenceValuePair(
                    curP.x,
                    curP.y,
                    curP.x.getAbstractVariable(curP.y),
                    this.targetState,
                    this.getNewRefName(curP.x, curP.y),
                    newVal);
        }

        return newVal;
    }

    /**
     * Intersect two arrays, two instances, or one of both.
     * @param stateA the first state
     * @param refA the reference for varA in stateA
     * @param varA the first variable (from <code>stateA</code>)
     * @param stateB the second state
     * @param refB the reference for varB in stateB
     * @param varB the second variable (from <code>stateB</code>)
     * @return the intersected array
     * @throws IntersectionFailException if intersection failed
     */
    private AbstractVariable intersectReferenceValuePair(
        final State stateA,
        final AbstractVariableReference refA,
        final AbstractVariable varA,
        final State stateB,
        final AbstractVariableReference refB,
        final AbstractVariable varB) throws IntersectionFailException
    {
        if (varA instanceof Array || varB instanceof Array) {
            return this.intersectArrays(stateA, refA, varA, stateB, refB, varB);
        }
        assert (varA == null || varA instanceof ObjectInstance);
        assert (varB == null || varB instanceof ObjectInstance);
        assert (varA != null || varB != null);
        return this.intersectInstances(stateA, refA, (ObjectInstance) varA, stateB, refB, (ObjectInstance) varB);
    }

    /**
     * Intersect if at least one of the two variables is some array.
     * @param stateA the first state
     * @param refA the reference for varA in stateA
     * @param varA the first variable (from <code>stateA</code>)
     * @param stateB the second state
     * @param refB the reference for varB in stateB
     * @param varB the second variable (from <code>stateB</code>)
     * @return the intersected array
     * @throws IntersectionFailException if intersection failed
     */
    private Array intersectArrays(
        final State stateA,
        final AbstractVariableReference refA,
        final AbstractVariable varA,
        final State stateB,
        final AbstractVariableReference refB,
        final AbstractVariable varB) throws IntersectionFailException
    {
        //Get the reference to the length:
        final AbstractVariableReference newLengthRef;
        if (varA instanceof Array) {
            newLengthRef = this.getNewRefName(stateA, ((Array) varA).getLength());
        } else {
            newLengthRef = this.getNewRefName(stateB, ((Array) varB).getLength());
        }

        if ((varA instanceof ConcreteArray) || (varB instanceof ConcreteArray)) {
            if (!newLengthRef.pointsToConstantInt()) {
                throw new IntersectionFailException("index of array must be a constant");
            }
            final ConcreteArray concreteResult = new ConcreteArray(newLengthRef, this.targetState, null);
            if (varA instanceof ConcreteArray && varB instanceof ConcreteArray) {
                final AbstractVariableReference[] concrDataA = ((ConcreteArray) varA).getData();
                final AbstractVariableReference[] concrDataB = ((ConcreteArray) varB).getData();
                if (concrDataA.length != concrDataB.length) {
                    throw new IntersectionFailException("Incompatible array length");
                }

                for (int index = 0; index < concrDataA.length; index++) {
                    AbstractVariableReference fieldRef;
                    if (stateA == this.targetState) {
                        fieldRef = concrDataA[index];
                    } else {
                        fieldRef = this.partition.getNewRefFor(stateA, concrDataA[index]);
                    }
                    concreteResult.put(index, fieldRef);
                }
            } else if (varA instanceof ConcreteArray) {
                final AbstractVariableReference[] concrDataA = ((ConcreteArray) varA).getData();
                for (int index = 0; index < concrDataA.length; index++) {
                    concreteResult.put(index, this.partition.getNewRefFor(stateA, concrDataA[index]));
                }
            } else if (varB instanceof ConcreteArray) {
                final AbstractVariableReference[] concrDataB = ((ConcreteArray) varB).getData();
                for (int index = 0; index < concrDataB.length; index++) {
                    AbstractVariableReference newRef;
                    if (stateB == this.targetState) {
                        newRef = concrDataB[index];
                    } else {
                        newRef = this.partition.getNewRefFor(stateB, concrDataB[index]);
                    }
                    concreteResult.put(index, newRef);
                }
            }
            return concreteResult;
        }
        return new AbstractArray(newLengthRef);
    }

    /**
     * Intersect for two instance, where neither is an array.
     * @param stateA the first state
     * @param refA the reference for varA in stateA
     * @param varA the first variable (from <code>stateA</code>)
     * @param stateB the second state
     * @param refB the reference for varB in stateB
     * @param varB the second variable (from <code>stateB</code>)
     * @return the intersected instance
     * @throws IntersectionFailException if intersection failed
     */
    private ObjectInstance intersectInstances(
        final State stateA,
        final AbstractVariableReference refA,
        final ObjectInstance varA,
        final State stateB,
        final AbstractVariableReference refB,
        final ObjectInstance varB) throws IntersectionFailException
    {
        final ClassPath cPath = this.targetState.getClassPath();

        final ClassName jloCN = ClassName.Important.JAVA_LANG_OBJECT.getClassName();
        final TypeTree jloType = cPath.getTypeTree(jloCN);

        // first of all, we need to intersect the types
        TypeTree aType;
        if (varA == null || varA instanceof AbstractInstance) {
            aType = jloType;
        } else {
            aType = ((ConcreteInstance) varA).getMostSpecializedInstance().getType();
        }

        TypeTree bType;
        if (varB == null || varB instanceof AbstractInstance) {
            bType = jloType;
        } else {
            bType = ((ConcreteInstance) varB).getMostSpecializedInstance().getType();
        }
        TypeTree intersectedType;
        if (aType.equals(bType)) {
            intersectedType = aType;
        } else if (aType.isProperSubClassOf(bType.getClassName())) {
            intersectedType = aType;
        } else if (bType.isProperSubClassOf(aType.getClassName())) {
            intersectedType = bType;
        } else {
            throw new IntersectionFailException("type: " + aType + " " + bType);
        }

        // Do the really easy case:
        if ((varA instanceof AbstractInstance && varB instanceof AbstractInstance)) {
            return new AbstractInstance();
        }

        final ConcreteInstance concreteResult =
            ConcreteInstance.newInstanceFromType(this.targetState, intersectedType, FieldValueSettings.NULL_VALUE);

        // find all fields that need to be intersected
        final Map<TypeTree, Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>>> fields =
            new LinkedHashMap<>();
        if (varA != null && varA instanceof ConcreteInstance) {
            ConcreteInstance current = (ConcreteInstance) varA;
            while (current != null) {
                final Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>> pair =
                    new Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>>(
                        new LinkedHashMap<>(current.getFields()),
                        null);
                fields.put(current.getType(), pair);
                current = current.getSubClassInstance();
            }
        }
        if (varB != null && varB instanceof ConcreteInstance) {
            ConcreteInstance current = (ConcreteInstance) varB;
            while (current != null) {
                Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>> pair =
                    fields.get(current.getType());
                if (pair == null) {
                    pair =
                        new Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>>(
                            null,
                            new LinkedHashMap<>(current.getFields()));
                    fields.put(current.getType(), pair);
                } else {
                    pair.y = current.getFields();
                }
                current = current.getSubClassInstance();
            }
        }

        for (final Map.Entry<TypeTree, Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>>> typeToFieldValues : fields
            .entrySet())
        {
            ConcreteInstance current = concreteResult;
            final TypeTree typeTree = typeToFieldValues.getKey();
            while (!current.getType().equals(typeTree)) {
                current = current.getSubClassInstance();
            }
            final Pair<Map<String, AbstractVariableReference>, Map<String, AbstractVariableReference>> maps =
                typeToFieldValues.getValue();
            if (maps.x != null && maps.y != null) {
                assert (varB != null);
                for (final Map.Entry<String, AbstractVariableReference> fieldValueA : maps.x.entrySet()) {
                    final String fieldName = fieldValueA.getKey();
                    ImmutableSet<StateAndRef> eqClass =
                        this.partition.getEquivalenceClass(stateA, fieldValueA.getValue());
                    AbstractVariableReference fieldResultRef;
                    if (eqClass == null) {
                        final AbstractVariableReference fieldValueB = maps.y.get(fieldName);
                        eqClass = this.partition.getEquivalenceClass(stateB, fieldValueB);
                        assert (eqClass != null);
                        fieldResultRef = this.getNewRefName(stateB, fieldValueB);
                    } else {
                        fieldResultRef = this.getNewRefName(stateA, fieldValueA.getValue());
                    }
                    assert (fieldResultRef != null);
                    current.setField(fieldName, fieldResultRef);
                }
            } else if (maps.x == null) {
                assert (maps.y != null);
                for (final Map.Entry<String, AbstractVariableReference> fieldValueB : maps.y.entrySet()) {
                    final String fieldName = fieldValueB.getKey();
                    final AbstractVariableReference fieldResultRef = this.getNewRefName(stateB, fieldValueB.getValue());
                    current.setField(fieldName, fieldResultRef);
                }
            } else {
                for (final Map.Entry<String, AbstractVariableReference> fieldValueA : maps.x.entrySet()) {
                    final String fieldName = fieldValueA.getKey();
                    final AbstractVariableReference fieldResultRef = this.getNewRefName(stateA, fieldValueA.getValue());
                    current.setField(fieldName, fieldResultRef);
                }
            }
        }

        return concreteResult;
    }

    /**
     * @param s some state
     * @param r some reference
     * @return a reference in <code>targetState</code> corresponding to the pair (s,r) (so if is the target state, it's
     * just r, otherwise the new name for (s,r).
     */
    private AbstractVariableReference getNewRefName(final State s, final AbstractVariableReference r) {
        if (s == this.targetState) {
            return r;
        }
        return this.partition.getNewRefFor(s, r);
    }

    /**
     * @param state some state
     * @param refs collection of references
     * @return true if all pairs of distinct references from <code>refs</code> are marked as possibly equal in
     * <code>state</code>.
     */
    private static boolean areAllPossiblyEqual(final State state, final Collection<AbstractVariableReference> refs) {
        if (refs.isEmpty()) {
            return true;
        }

        final EqualityGraph eqGraph = state.getHeapAnnotations().getEqualityGraph();

        for (final AbstractVariableReference r1 : refs) {
            for (final AbstractVariableReference r2 : refs) {
                if (!r1.equals(r2) && !eqGraph.areMarkedAsPossiblyEqual(r1, r2)) {
                    return false;
                }
            }
        }

        return true;
    }

    /**
     * @param ref a reference
     * @param heapPos the heap positions of the state
     * @return a subset of all realized cycles that can be reached from the given reference. Each element in the set
     * corresponds to a cycle, where the inner collection gives (a superset of) the edges which are needed for this
     * cycle.
     */
    private static Collection<Collection<HeapEdge>> getRealizedCycles(
        final AbstractVariableReference ref,
        final HeapPositions heapPos)
    {
        final Collection<Collection<HeapEdge>> result = new LinkedHashSet<>();

        if (ref.isNULLRef()) {
            return result;
        }

        for (final AbstractVariableReference reachedRef : Reachability.getReachableRefs(ref, false, heapPos.getState()))
        {
            for (final StatePosition pos : heapPos.getPositionsForRef(reachedRef)) {
                final Collection<NonRootPosition> continuations = heapPos.getContinuations(pos);
                if (continuations != null) {
                    for (final NonRootPosition continuation : continuations) {
                        result.add(continuation.getHeapEdges());
                    }
                }
            }
        }
        return result;
    }

    /**
     * @param ref some reference
     * @param heapPositions the heap positions object of the state to investigate
     * @return true only if there is some realized non-tree shape below the given reference
     */
    private static boolean hasRealizedNonTree(final AbstractVariableReference ref, final HeapPositions heapPositions) {
        if (ref.isNULLRef()) {
            return false;
        }
        for (final StatePosition posOfRef : heapPositions.getPositionsForRef(ref)) {
            for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> entry : heapPositions
                .getRefsWithMultiplePositions()
                .entrySet())
            {
                boolean foundOne = false;
                for (final StatePosition pos : entry.getValue()) {
                    if (posOfRef.isPrefixOf(pos)) {
                        // there is one path from ref to entry.getKey()
                        if (foundOne) {
                            // we already know another path
                            return true;
                        }
                        foundOne = true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * @param s some state
     * @return the heap positions (without primitives) corresponding to this state's heap
     */
    private HeapPositions getHeapPosFor(final State s) {
        HeapPositions heapPos = this.heapPosCache.get(s);
        if (heapPos == null) {
            heapPos = new HeapPositions(s);
            this.heapPosCache.put(s, heapPos);
        }
        return heapPos;
    }
}
