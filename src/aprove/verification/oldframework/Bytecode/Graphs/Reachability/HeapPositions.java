package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class can be used to get information about state positions (or "paths")
 * reaching specific references to object instances or arrays. Using this
 * information it is easy to detect cycles or non-tree shapes in general. There
 * is also a mode where the primitive types are regarded, too.
 * <p>
 * Since a state containing a cycle has infinitely many state positions, we need
 * to do some tricks here. In general we only need the maximal realized prefix
 * of all positions for a certain reference. Because of this it suffices to only
 * store positions that do not represent any traversed cycle and consider the
 * cycles while computing the (realized?) references represented by a position.
 * If a state position results out of a state with cycles and we now retrieve
 * the references for this position in some other state, we get several
 * references if the state in question does not realize all the cycles that are,
 * in some sense, part of the state position.
 * <p>
 * For each reference the set of state positions does not include two positions
 * p, q where p is a prefix of q (or the other way around). Moreover, for a
 * given state no state position is created that represents a full cycle
 * traversal. Information about cycles can be found in a dedicated field, which
 * is regarded when receiving the references corresponding to some state
 * position using the method getMaxRealizedPrefixes().
 * @author Carsten Otto
 */
public class HeapPositions {
    /**
     * For the positions we encountered, we also store the references at these
     * positions.
     */
    private final Map<StatePosition, AbstractVariableReference> posToRefCache;

    /**
     * For all known references the corresponding positions are stored.
     */
    private final CollectionMap<AbstractVariableReference, StatePosition> refToPosition;

    /**
     * The state we are working on.
     */
    private final State state;

    /**
     * For position leading to a reference starting a cycle (meaning this is the
     * first reference visited twice when traversing the cycle) we remember the
     * (fake) non-root position representing a run through the cycle. As an
     * example, for x.f=y and y.g=x we store "fg" as a position for x. Since the key
     * is a state position, for references that are reachable using different
     * paths (even when ignoring cycles), several entries are provided here.
     * This cannot be changed to references as keys, since the references change
     * from state to state. When requesting cycle information from state A
     * (which was used to construct this object) while working on state B, the
     * key must be something which is the same in A and B.
     */
    private final CollectionMap<StatePosition, NonRootPosition> cycleContinuations;

    /**
     * Cache the computed prefixes from getMaxRealizedPrefixes
     */
    private final Map<HeapPositions, CollectionMap<StatePosition, PrefixResult>> prefixCache;

    /**
     * Cache the references that have multiple positions
     */
    private CollectionMap<AbstractVariableReference, StatePosition> refsWithMultiplePositions;

    /**
     * Cache results of the method getAllNeededEdges()
     */
    private final Map<Pair<AbstractVariableReference, AbstractVariableReference>, Collection<HeapEdge>> allNeededEdgesCache;

    /**
     * Create information about all references reachable from all root
     * positions. Depending on the argument this instance also contains
     * primitive values.
     * @param stateParam the state for which the instance is created
     * @param primitives iff true also primitive values are added.
     */
    public HeapPositions(final State stateParam, final boolean primitives) {
        this.refsWithMultiplePositions = null;
        this.prefixCache = new LinkedHashMap<>();
        this.posToRefCache = new LinkedHashMap<>();
        this.allNeededEdgesCache = new LinkedHashMap<>();
        this.state = stateParam;
        this.refToPosition = new CollectionMap<>();
        this.cycleContinuations = new CollectionMap<>();

        // collect all root positions
        Collection<RootPosition> todo = collectRootPositions(stateParam);

        /*
         * Complete state traversing, starting collecting at the collected root
         * positions.
         */
        for (final StatePosition pos : todo) {
            final AbstractVariableReference ref = stateParam.getReference(pos);
            this.complete(ref, pos, primitives);
        }
    }

    /**
     * Create information about all references reachable from all root
     * positions. Primitive values and not are not contained.
     * @param stateParam the state for which the instance is created
     */
    public HeapPositions(final State stateParam) {
        this(stateParam, false);
    }

    /**
     * @param ref a reference
     * @return true if <code>ref</code> appears in the represented heap.
     */
    public boolean containsRef(final AbstractVariableReference ref) {
        return this.refToPosition.containsKey(ref);
    }

    public static List<RootPosition> collectRootPositions(State state) {
        ClassPath cPath = state.getClassPath();
        List<RootPosition> res = new LinkedList<>();
        for (final ClassName cn : state.getStaticFields().getClasses()) {
            for (final Map.Entry<String, Field> pair : cPath.getClass(cn).getStaticFields().entrySet()) {
                final String fieldName = pair.getKey();
                final RootPosition pos = StaticFieldRootPosition.create(new FieldIdentifier(cn, fieldName));
                res.add(pos);
            }
        }
        final CallStack callStack = state.getCallStack();
        final int size = callStack.size();
        for (int frameNum = 0; frameNum < size; frameNum++) {
            final StackFrame sf = state.getCallStack().get(frameNum);

            for (final InputReference ir : state.getCallStack().get(frameNum).getInputReferences()) {
                res.add(ir.getIRStatePosition(frameNum));
            }

            if (sf.hasException()) {
                final RootPosition pos = ExceptionRootPosition.create(frameNum);
                res.add(pos);
            }
            for (final int varNum : sf.getActiveVariables()) {
                final RootPosition pos = LocVarRootPosition.create(frameNum, varNum);
                res.add(pos);
            }
            for (int varNum = 0; varNum < sf.getOperandStack().getStack().size(); varNum++) {
                final RootPosition pos = OpStackRootPosition.create(frameNum, varNum);
                res.add(pos);
            }
        }
        return res;
    }

    /**
     * Continue traversing the heap at the given position and reference and add
     * references/positions accordingly.
     * @param pos the position to start at
     * @param ref the reference at the given position
     * @param primitives iff true, the instance also contains primitive values.
     */
    private void complete(final AbstractVariableReference ref, final StatePosition pos, final boolean primitives) {
        if (!primitives && ref.isNULLRef()) {
            return;
        }
        if (ref.isNULLRef() || this.state.getHeapAnnotations().isMaybeExisting(ref) || ref instanceof ReturnAddress) {
            if (!(ref instanceof ReturnAddress) || primitives) {
                this.extend(ref, pos);
            }
            // nothing more to do
            return;
        }
        final AbstractVariable var = this.state.getAbstractVariable(ref);
        if (var instanceof AbstractNumber) {
            if (primitives) {
                this.extend(ref, pos);
            }
            return;
        }
        final Collection<StatePosition> positions = this.refToPosition.get(ref);
        if (pos instanceof NonRootPosition && positions != null) {
            // we already found a path to this reference - are we dealing with a cycle?
            for (final StatePosition otherPos : positions) {
                if (pos == otherPos) {
                    continue;
                }
                /*
                 * We do not want to run through cycles, but we want to know
                 * where cycles are.
                 */
                if (otherPos.isPrefixOf(pos)) {
                    // we traversed a cycle!
                    this.cycleContinuations.add(otherPos, pos.getSuffixOf(otherPos));
                    return;
                }
            }
        }
        this.extend(ref, pos);
        if (var instanceof Array) {
            final Array array = (Array) var;
            if (primitives) {
                final StatePosition newPos = pos.appendArrayLength();
                this.complete(array.getLength(), newPos, primitives);
            }
            if (array instanceof AbstractArray) {
                return;
            }
            final ConcreteArray concArr = (ConcreteArray) array;
            final int length = concArr.getLiteralLength();
            for (int index = 0; index < length; index++) {
                final AbstractVariableReference childRef = concArr.get(this.state, ref, index);
                final StatePosition newPos = pos.appendArrayElement(index);
                this.complete(childRef, newPos, primitives);
            }
            return;
        }
        if (var instanceof ObjectInstance) {
            if (var instanceof AbstractInstance) {
                return;
            }
            final ConcreteInstance ai = (ConcreteInstance) var;
            for (final Map.Entry<FieldIdentifier, AbstractVariableReference> entry : ai.getAllFields().entrySet()) {
                if (entry.getValue() != null) {
                    final StatePosition newPos = pos.appendField(entry.getKey());
                    this.complete(entry.getValue(), newPos, primitives);
                }
            }
        }
    }

    /**
     * Add the given reference to the instance.
     * @param ref the reference to add
     * @param pos the state position that can be used to reach the given
     * reference
     */
    private void extend(final AbstractVariableReference ref, final StatePosition pos) {
        final AbstractVariableReference oldRef = this.posToRefCache.put(pos, ref);
        assert (oldRef == null || oldRef.equals(ref));
        this.refToPosition.add(ref, pos);
    }

    /**
     * Keep in mind that the positions returned here are a subset of all
     * (infinite?) positions that are defined for the reference. Algorithms must
     * deal with that, see the comment for this class.
     * @param ref a reference
     * @return the positions known for the given reference
     */
    public Collection<StatePosition> getPositionsForRef(final AbstractVariableReference ref) {
        final Collection<StatePosition> result = this.refToPosition.get(ref);
        assert (result != null) : "Could not find pos for ref " + ref + " in state: " + this.state;
        return result;
    }

    /**
     * If a reference has two positions in a state where no cycle is involved in
     * these positions, this reference and at least those two positions are part
     * of the result.
     * <p>
     * For references with at least two positions because of cycles we only add
     * those references to the result that are <b>on</b> some cycle. For each
     * path to this cycle (where the path does not traverse a cycle!), we add
     * the positions
     * <ul>
     * <li>1) that first leads to the cycle and then to the reference, and</li>
     * <li>2) the position that leads to the cycle, then to the reference, then
     * through the remainder of the cycle again to the reference</li>
     * </ul>
     * So, position 2 is a suffix of position 1.
     * <p>
     * Attention: This method does not consider references that have two
     * positions only resulting out of adding a different number of cycle
     * traversals somewhere "before" (i.e. if s|root = s|root.f we do not
     * consider that the reference at s|root.g has two positions root.g and
     * root.f.g (and root.f.f.g...). However, we return root and root.f as two
     * positions for the reference at s|root, because this reference is
     * <b>on</b> a cycle).
     * @return the references and the corresponding positions where at least two
     * positions are known. Attention: for cycles only a very limited subset of
     * positions is considered.
     */
    public CollectionMap<AbstractVariableReference, StatePosition> getRefsWithMultiplePositions() {
        if (this.refsWithMultiplePositions != null) {
            return this.refsWithMultiplePositions;
        }

        final CollectionMap<AbstractVariableReference, StatePosition> result = new CollectionMap<>();

        // start with the references where we have at least two explicit positions
        for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> e : this.refToPosition.entrySet()) {
            final AbstractVariableReference ref = e.getKey();
            final Collection<StatePosition> coll = e.getValue();
            assert (coll != null);
            if (coll.size() > 1) {
                result.add(ref, coll);
            }
        }

        /*
         * So far we only covered the references that have at least two
         * positions where each position does not include a run through any
         * cycle. We also need the positions that result out of a single run
         * through a cycle, so we run through each cycle once now.
         *
         * We need to run along the cycle and, for every reference on it, add a
         * single cycle run to its position. Here it suffices to prolong these
         * positions that are a suffix of cyclicPos (the other positions
         * introduced by different paths  will be handled in other loop
         * iterations).
         *
         * For a continuation of 123 (meaning: when starting somewhere and going
         * 123 you end up where you started) and cyclicPos being 0 we build
         * 0.eps.123.eps, 0.1.23.1, and 0.12.3.12. Here, the second and last
         * component are identical and the first and second together form the
         * continuation.
         */
        final CollectionMap<StatePosition, Pair<NonRootPosition, NonRootPosition>> continuationSplits =
            new CollectionMap<>();
        for (final NonRootPosition continuation : this.cycleContinuations.allValues()) {
            final int cycleLength = continuation.length();
            for (int i = cycleLength; i > 0; i--) {
                // build (eps,123), (1,23), and (12,3) for a continuation of 123
                final Pair<NonRootPosition, NonRootPosition> split = continuation.split(i);
                continuationSplits.add(continuation, split);
            }
        }

        for (final Entry<StatePosition, Collection<NonRootPosition>> entry : this.cycleContinuations.entrySet()) {
            final StatePosition cyclicPos = entry.getKey();
            for (final NonRootPosition continuation : entry.getValue()) {
                for (final Pair<NonRootPosition, NonRootPosition> split : continuationSplits.get(continuation)) {
                    /*
                     * Build up the longer position from the end (from
                     * cyclicPos to some reference and a complete run
                     * through the cycle from there).
                     */
                    final StatePosition longerPos = cyclicPos.append(split.x).append(split.y).append(split.x);
                    final StatePosition origPos = cyclicPos.append(split.x);

                    final AbstractVariableReference refOnCycle = this.posToRefCache.get(origPos);
                    result.add(refOnCycle, origPos);
                    result.add(refOnCycle, longerPos);
                }
            }
        }

        this.refsWithMultiplePositions = result;

        return result;
    }

    /**
     * @return the state for which this instance was constructed
     */
    public State getState() {
        return this.state;
    }

    /**
     * For the given state position <code>pos</code>, compute the maximal
     * realized prefix in the state used to build <code>this</code>
     * HeapPositions object. Example: for a position LV00.f.g.h where only LV.f
     * is realized in this state, the prefix LV.f with a unrealized suffix #.g.h
     * is returned, together with the reference at LV.f.
     * <p>
     * The second argument <code>heapPositions</code> is used to work with
     * cyclic structures. If the argument <code>pos</code> describes a reference
     * with a realized cycle in the state which was used to construct
     * <code>heapPositions</code>, all corresponding cycles are regarded as
     * follows:
     * </p>
     * <p>
     * Whenever a reference is reached where a cycle is started (that leads back
     * to x), we also run through that cycle. This is done in addition to the
     * original position we asked for (e.g. the position that ignores the cycle
     * at x and continues along some acyclic path). If the cycle cannot be
     * traversed fully, we denote that in the result set. For "failed" results
     * that exist due to non-realized cycles, the suffix only gives information
     * about the cycle that was investigated without giving any information
     * about the remainder of the position (in the example above the part of the
     * position that ignores the cycle and runs past it). Therefore, it cannot
     * be realy used.
     * </p>
     * @param pos some position
     * @param heapPositions the heap position object for some state where the
     * argument position was taken from. This object is used to get information
     * about cycles that are implicitly part of the position.
     * @return the references that can be reached by following the given
     * position as long as possible (including cycles). For positions that are
     * not fully realized in this state, the PrefixResult object also gives the
     * longest realized prefix and the suffix that is not realized.
     */
    public Collection<PrefixResult> getMaxRealizedPrefixes(final StatePosition pos, final HeapPositions heapPositions) {
        CollectionMap<StatePosition, PrefixResult> innerMap = this.prefixCache.get(heapPositions);
        if (innerMap != null) {
            final Collection<PrefixResult> cachedResults = innerMap.get(pos);
            if (cachedResults != null) {
                return cachedResults;
            }
        } else {
            innerMap = new CollectionMap<>();
            this.prefixCache.put(heapPositions, innerMap);
        }

        final CollectionMap<StatePosition, NonRootPosition> seenCycles = new CollectionMap<>();
        final Collection<PrefixResult> results =
            this.getMaxRealizedPrefixes(
                new Pair<StatePosition, StatePosition>(null, pos),
                seenCycles,
                heapPositions,
                new Pair<StatePosition, StatePosition>(null, pos));

        innerMap.put(pos, results);

        return results;
    }

    /**
     * Check all prefixes of the given position and find out where traversals
     * according to these positions ends in this state. Here, also all possible
     * cycles are regarded, so that a single state position may result in both a
     * successful path (avoiding the cycle) and an unsuccessful path (running
     * into the cycle and failing in there).
     * @param posAndTarget the last known good position and the final position
     * we want to reach
     * @param seenCycles it is possible to run into cycles infinitely often, so
     * we remember which cycles we already handled to finish in finite time
     * @param heapPositions the HeapPosition object used to create the
     * corresponding position (used to get information about cycles that need to
     * be checked)
     * @param posAndTargetOther the last known good position and the final
     * position we want to reach (wrt. the state of heapPositions)
     * @return the prefix results indicating where the position leads to and how
     * following the path failed in the state (which may be due to cycles not
     * explictly represented in targetPosition)
     */
    private Collection<PrefixResult> getMaxRealizedPrefixes(
        final Pair<StatePosition, StatePosition> posAndTarget,
        final CollectionMap<StatePosition, NonRootPosition> seenCycles,
        final HeapPositions heapPositions,
        final Pair<StatePosition, StatePosition> posAndTargetOther)
    {
        StatePosition lastGoodPos = posAndTarget.x;
        StatePosition lastGoodPosOther = posAndTargetOther.x;
        final StatePosition targetPos = posAndTarget.y;
        final StatePosition targetPosOther = posAndTargetOther.y;

        final Collection<PrefixResult> results = new LinkedHashSet<>();

        /*
         * Check each prefix position (and cycles starting there!) until the
         * target position is reached.
         */
        for (final Iterator<StatePosition> it = targetPos.getPathToRoot().descendingIterator(); it.hasNext();) {
            //        for (final StatePosition currentPos : targetPos.getPathFromRoot()) {
            final StatePosition currentPos = it.next();
            /*
             * When being called with the task of checking a cycle, we can skip
             * the parts that we already checked.
             */
            if (lastGoodPos != null && currentPos.isPrefixOf(lastGoodPos)) {
                continue;
            }

            StatePosition currentPosOther;
            if (lastGoodPos == null) {
                currentPosOther = currentPos;
            } else {
                final NonRootPosition suffix = currentPos.getSuffixOf(lastGoodPos);
                currentPosOther = lastGoodPosOther.append(suffix);
            }

            final AbstractVariableReference ref = this.posToRefCache.get(currentPos);
            if (ref == null) {
                /*
                 * This can mean two things. The easy alternative is that the
                 * position we asked for is not present in this state, even when
                 * considering the theoretical, full (infinite?) set of
                 * positions.
                 * The other alternative is that the last part of the current
                 * position corresponds to a complete cycle run. Since these
                 * cycle runs are not represented explictly in this data
                 * structure, we detect positions ending in a full cycle run and
                 * shorten the position accordingly. We then check this
                 * shortened position, which also regards tests if the cycle is
                 * realized (although this "question" is not explicitly stated
                 * in the state position anymore).
                 */

                final Pair<StatePosition, StatePosition> withoutCycle = this.removeCycle(currentPos, targetPos);

                if (withoutCycle != null) {
                    /*
                     * We were looking at a position ending with a full cycle
                     * traversal. This full cycle run now is removed from the
                     * target position and we can continue normally.
                     */

                    final Pair<StatePosition, StatePosition> withoutCycleOtherTemp =
                        heapPositions.removeCycle(currentPosOther, targetPosOther);
                    Pair<StatePosition, StatePosition> withoutCycleOther;
                    if (withoutCycleOtherTemp == null) {
                        withoutCycleOther = new Pair<>(currentPosOther, targetPosOther);
                    } else {
                        withoutCycleOther = withoutCycleOtherTemp;
                    }

                    return this.getMaxRealizedPrefixes(withoutCycle, seenCycles, heapPositions, withoutCycleOther);
                }

                /*
                 * We found some unrealized part in the state so that we cannot
                 * follow the path.
                 */
                if (lastGoodPos == null) {
                    /*
                     * We have have asked for some position where even the root
                     * position is not existent. This is OK, if we have null
                     * there.
                     */
                    assert (currentPos.getFromState(this.state).isNULLRef());
                    final PrefixResult resultfoo = new PrefixResult(AbstractVariableReference.NULLREF, null, targetPos);
                    return Collections.singleton(resultfoo);
                }
                final PrefixResult resultfoo =
                    new PrefixResult(
                        this.posToRefCache.get(lastGoodPos),
                        lastGoodPos,
                        targetPos.getSuffixOf(lastGoodPos));
                return Collections.singleton(resultfoo);
            }
            /*
             * The position is realized in this state. If there is a cycle
             * starting in that position, also ensure that it can be traversed.
             */
            lastGoodPos = currentPos;
            final Pair<StatePosition, StatePosition> posAndTargetNew = new Pair<>(lastGoodPos, targetPos);

            lastGoodPosOther = currentPosOther;
            // FIXME cut out cycles from currentPosOther and targetOther
            final Pair<StatePosition, StatePosition> posAndTargetOtherNew = new Pair<>(lastGoodPos, targetPos);

            results.addAll(this.traverseCycles(posAndTargetNew, heapPositions, posAndTargetOtherNew, seenCycles));
        }
        /*
         * We managed to follow the whole path and for every cycle checked that
         * it can be traversed, too (which may have caused failed results
         * already added to 'results').
         */
        results.add(new PrefixResult(this.posToRefCache.get(lastGoodPos), lastGoodPos));

        return results;
    }

    /**
     * The given position is realized. Since cycles are not represented
     * explicitly in the todo list (or were removed earlier), we also check if
     * all cycles starting in the current position can be traversed.
     * @param posAndTarget the last known good position and the final position
     * we want to reach
     * @param heapPositions the HeapPosition object used to create the
     * corresponding position (used to get information about cycles that need to
     * be checked)
     * @param posAndTargetOther the last known good position and the final
     * position we want to reach (wrt. the state of heapPositions)
     * @param seenCycles it is possible to run into cycles infinitely often, so
     * we remember which cycles we already handled to finish in finite time
     * @return the prefix results that indicate that some cycle cannot be
     * traversed fully
     */
    private Collection<PrefixResult> traverseCycles(
        final Pair<StatePosition, StatePosition> posAndTarget,
        final HeapPositions heapPositions,
        final Pair<StatePosition, StatePosition> posAndTargetOther,
        final CollectionMap<StatePosition, NonRootPosition> seenCycles)
    {

        final StatePosition lastGoodPos = posAndTarget.x;
        final StatePosition lastGoodPosOther = posAndTargetOther.x;

        final Collection<PrefixResult> result = new LinkedHashSet<>();

        /*
         * We need to check if the current state also contains the cycle
         * defined in heapPositions.
         */
        final Collection<NonRootPosition> continuations = heapPositions.cycleContinuations.get(lastGoodPosOther);
        if (continuations == null) {
            // no cycle, nothing to do
            return result;
        }

        /*
         * This is what was still left from the previous task (and will be
         * ignored in the cycle traversal!)
         */
        final StatePosition targetPositionOther = posAndTargetOther.y;
        final NonRootPosition remainder = targetPositionOther.getSuffixOf(lastGoodPosOther);

        /*
         * According to the other state, a cycle starts at the current position.
         * We are only allowed to consider the position "fully realized" if it
         * also is able to traverse the cycle(s).
         */
        final AbstractVariableReference ref = this.posToRefCache.get(lastGoodPos);
        for (final NonRootPosition continuation : continuations) {
            if (!seenCycles.add(lastGoodPosOther, continuation)) {
                /*
                 * No need to run into a cycle twice (this works since we remove
                 * full cycle runs at the end of the position, i.e. for a cycle
                 * fg the position a.f.g is reduced to a, so that we never have
                 * a, a.f.g, a.f.g.f.g, ... (but two times "a" where we try to
                 * append fg)).
                 */
                continue;
            }
            // also run through the cycle once
            final StatePosition newTarget = lastGoodPos.append(continuation);
            final StatePosition newTargetOther = lastGoodPosOther.append(continuation);
            final Pair<StatePosition, StatePosition> posAndTargetNew = new Pair<>(lastGoodPos, newTarget);
            final Pair<StatePosition, StatePosition> posAndTargetOtherNew =
                new Pair<>(lastGoodPosOther, newTargetOther);

            final Collection<PrefixResult> newResult =
                this.getMaxRealizedPrefixes(posAndTargetNew, seenCycles, heapPositions, posAndTargetOtherNew);

            for (final PrefixResult temp : newResult) {
                if (temp.isRealized()) {
                    /*
                     * We managed to run through the cycle - but did we close
                     * the cycle (i.e., reach the start again)?
                     */
                    if (!ref.equals(temp.getReference())) {
                        /*
                         * No. We ran through the cycle, but ended up somewhere
                         * else. As a consequence the remainder of the original
                         * task cannot be considered realized.
                         */
                        result.add(new PrefixResult(temp.getReference(), temp.getPosition(), remainder));
                    }
                    // otherwise we ran through the cycle, which is not interesting
                } else {
                    /*
                     * We were unable to traverse the cycle, how far did we go?
                     * What is missing?
                     */
                    // the part of the cycle that is missing
                    final NonRootPosition unrealizedCyclePart = (NonRootPosition) temp.getUnrealizedPosition();
                    NonRootPosition newUnrealized;
                    if (unrealizedCyclePart == null) {
                        newUnrealized = remainder;
                    } else {
                        newUnrealized = (NonRootPosition) unrealizedCyclePart.append(remainder);
                    }
                    final PrefixResult newPR = new PrefixResult(temp.getReference(), temp.getPosition(), newUnrealized);
                    result.add(newPR);
                }
            }
        }
        return result;
    }

    /**
     * If the last n elements of the current position represent a full cycle
     * traversal, remove that from the current position and the target
     * position.
     * @param currentPosition the current position that may end with a full
     * cycle traversal
     * @param targetPosition the target position that should be reached finally
     * @return null if no cycle was found at the end of the current position,
     * otherwise return the current position and the target position, where a
     * cycle at the end of the current position was removed (and the target
     * position was adapted accordingly).
     */
    private Pair<StatePosition, StatePosition> removeCycle(
        final StatePosition currentPosition,
        final StatePosition targetPosition)
    {
        assert (targetPosition == null || currentPosition.isPrefixOf(targetPosition));
        final List<StatePosition> toRoot = currentPosition.getPathToRoot();
        for (final StatePosition prefixPos : toRoot) {
            final Collection<NonRootPosition> continuations = this.cycleContinuations.get(prefixPos);
            if (continuations == null) {
                // the prefix position does not start a cycle, continue with the next prefix
                continue;
            }
            for (final NonRootPosition continuation : continuations) {
                if (prefixPos.append(continuation).equals(currentPosition)) {
                    if (targetPosition != null) {
                        final StatePosition newTargetPos =
                            prefixPos.append(targetPosition.getSuffixOf(currentPosition));
                        return new Pair<>(prefixPos, newTargetPos);
                    }
                    return new Pair<>(prefixPos, null);
                }
            }
        }
        return null;
    }

    /**
     * The position must be represented, so in case of cycles this may not be
     * the case. Do NOT use with positions that contain a complete cycle run.
     * @param pos some state position
     * @param failOK if false, there must be a reference for pos
     * @return the reference for the given position
     */
    public AbstractVariableReference getReferenceForPos(final StatePosition pos, final boolean failOK) {
        final AbstractVariableReference result = this.posToRefCache.get(pos);
        assert (failOK || result != null);
        return result;
    }

    /**
     * @param pos a state position
     * @return the continuations leading from the reference defined by the
     * position to the same reference again (running through a cycle).
     */
    public Collection<NonRootPosition> getContinuations(final StatePosition pos) {
        Collection<NonRootPosition> res = new LinkedHashSet<>();
        if (this.cycleContinuations.containsKey(pos)) {
            // add all cycles that start at pos
            res.addAll(this.cycleContinuations.get(pos));
        }
        // check if pos is somewhere in the middle of a cycle
        Collection<StatePosition> toRoot = pos.getPathToRoot();
        for (StatePosition cur : toRoot) {
            if (this.cycleContinuations.containsKey(cur)) {
                // there are cycles that start at position cur, which is a prefix of pos
                Collection<NonRootPosition> curCycles = this.cycleContinuations.get(cur);
                for (NonRootPosition cycle : curCycles) {
                    if (pos.isPrefixOf(cur.append(cycle))) {
                        // this cycle runs through pos
                        int suffixLength = pos.length() - cur.length();
                        if (suffixLength == cycle.length()) {
                            // pos represents a full traversal of the cycle
                            res.add(cycle);
                        } else {
                            // modify the cycle to obtain the cycle leading from s|pos to s|pos
                            Pair<NonRootPosition, NonRootPosition> p = cycle.split(cycle.length() - suffixLength);
                            res.add((NonRootPosition) p.y.append(p.x));
                        }
                    }
                }
            }
        }
        return res;
    }

    /**
     * The position must be represented, so in case of cycles this may not be
     * the case. Do NOT use with positions that contain a complete cycle run.
     * @param pos some state position
     * @return the reference for the given position
     */
    public AbstractVariableReference getReferenceForPos(final StatePosition pos) {
        return this.getReferenceForPos(pos, false);
    }

    /**
     * Do not modify.
     * @return the known references with the positions (which is a subset of all
     * positions!)
     */
    public CollectionMap<AbstractVariableReference, StatePosition> getReferencesAndPositions() {
        return this.refToPosition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.state.toString();
    }

    /**
     * @param ref some reference
     * @return a shortest position for the given reference
     */
    public StatePosition getShortestPositionForRef(final AbstractVariableReference ref) {
        final Collection<StatePosition> coll = this.refToPosition.getNotNull(ref);
        assert (!coll.isEmpty());
        final TreeSet<StatePosition> treeSet = new TreeSet<>(coll);
        return treeSet.iterator().next();
    }

    /**
     * @param ref a reference
     * @param includeRef if set, also add ref to the result
     * @return a collection of all references that can concretely reach <code>ref</code>, including those on cycles
     * along the way
     */
    public Collection<AbstractVariableReference> getAllPredecessors(
        final AbstractVariableReference ref,
        final boolean includeRef)
    {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        this.getAllPredecessors(ref, result);
        if (includeRef) {
            result.add(ref);
        }
        return result;
    }

    /**
     * Collect all unseen references which are predecessors of the given reference.
     * @param ref a reference
     * @param seen the references that were already found
     */
    private void getAllPredecessors(
        final AbstractVariableReference ref,
        final Collection<AbstractVariableReference> seen)
    {
        final Collection<StatePosition> positions = this.getPositionsForRef(ref);
        final Collection<StatePosition> add = new LinkedHashSet<>();
        if (!positions.isEmpty()) {
            for (final StatePosition pos : positions) {
                final Collection<NonRootPosition> continuations = this.cycleContinuations.get(pos);
                if (continuations == null) {
                    continue;
                }
                for (final NonRootPosition nrp : this.cycleContinuations.get(pos)) {
                    add.add(pos.append(nrp));
                }
            }
        }
        positions.addAll(add);

        for (final StatePosition sPos : positions) {
            final List<StatePosition> toRoot = sPos.getPathToRoot();
            if (toRoot.size() > 1) {
                final StatePosition pred = toRoot.get(1);
                final AbstractVariableReference predRef = this.getReferenceForPos(pred);
                if (!seen.add(predRef)) {
                    continue;
                }
                this.getAllPredecessors(predRef, seen);
            }
        }
    }

    /**
     * @param pos some position
     * @param heapPositions the heap position object for some state where the
     * argument position was taken from. This object is used to get information
     * about cycles that are implicitly part of the position.
     * @return the references at s|pos'BAR (the longest prefix of pos' so that s
     * reaches a reference) for all pos' defined by pos and the state for which
     * the heapPositions argument was constructed (pos' may include more
     * positions due to cycles).
     */
    public Collection<AbstractVariableReference> getMaxRealizedReferences(
        final StatePosition pos,
        final HeapPositions heapPositions)
    {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final PrefixResult prefixResult : this.getMaxRealizedPrefixes(pos, heapPositions)) {
            result.add(prefixResult.getReference());
        }
        return result;
    }

    /**
     * The idea of this method is to return paths from start to end which
     * traverse as many edges as possible (by running through cycles). For each
     * such set of edges we then can check if there is a joins annotation that
     * allows the set of heap edges.
     * <p>
     * If traverseCycles is set to false, we find a collection of shortest
     * paths. This information then can be used to find out which edges must
     * exist on every possible connection between start and end.
     * <p>
     * Due to branches in the heap (diamond shapes) there may be different paths
     * from start to end, where the sets of used heap edges are incomparable or
     * disjoint. In order to better find missing joins annotations, for each
     * such alternative path a separate set is returned.
     * <p>
     * For the application of finding missing joins annotations, it is always
     * allowed to return smaller and/or less sets of heap edges. Because this
     * method is also used to find all possible edges from start to end (by
     * taking the union of all sets, see getPossibleHeapEdges()), we are not
     * allowed to ignore paths or cycles.
     * @param start a reference
     * @param end a reference
     * @param traverseCycles iff true, we also gather the edges that "hide" on
     * cycles along the path.
     * @return sets of edges that can be traversed when going from start to end
     */
    public Collection<Set<HeapEdge>> getNeededConnections(
        final AbstractVariableReference start,
        final AbstractVariableReference end,
        final boolean traverseCycles)
    {
        final Collection<Set<HeapEdge>> result = new LinkedHashSet<>();
        for (final StatePosition startPos : this.getPositionsForRef(start)) {
            for (final StatePosition endPos : this.getPositionsForRef(end)) {
                if (startPos.isPrefixOf(endPos)) {
                    final NonRootPosition suffix = endPos.getSuffixOf(startPos);

                    final Set<HeapEdge> set = new LinkedHashSet<>();
                    if (suffix != null) {
                        set.addAll(suffix.getHeapEdges());
                    }

                    // also add the edges on reachable (sub)cycles
                    final LinkedList<StatePosition> todo = new LinkedList<>();
                    todo.addAll(endPos.getPositionsDownTo(startPos));
                    while (!todo.isEmpty()) {
                        final StatePosition current = todo.pop();
                        final Collection<NonRootPosition> continuations = this.cycleContinuations.get(current);
                        if (traverseCycles && continuations != null) {
                            for (final NonRootPosition continuation : continuations) {
                                set.addAll(continuation.getHeapEdges());
                                todo.add(current.append(continuation));
                            }
                        }
                    }
                    if (!set.isEmpty()) {
                        result.add(set);
                    }
                }
            }
        }
        return result;
    }

    /**
     * Assume some path from start to end, maybe including cycle traversals.
     * Name the set of heap edges on this path S. Then S is a subset of the
     * edges returned by this method.
     * @param start a reference
     * @param end a reference
     * @return a set of all heap edges that can be traversed while going from
     * start to end. This is an overapproximation, i.e. if there is a path using
     * a heap edge, this edge is included.
     */
    public
        Set<HeapEdge>
        getPossibleHeapEdges(final AbstractVariableReference start, final AbstractVariableReference end)
    {
        final Set<HeapEdge> result = new LinkedHashSet<>();
        for (final Set<HeapEdge> set : this.getNeededConnections(start, end, true)) {
            result.addAll(set);
        }
        if (result.isEmpty()) {
            this.getPossibleHeapEdges(start, end);
        }
        assert (!result.isEmpty());
        return result;
    }

    /**
     * @param realizedPosParam the last reference in the state that could be
     * reached for some position
     * @param suffix the unrealized part of the position
     * @return all heap edges that may be traversed by going along the
     * unrealized suffix. This includes all possible cycle runs!
     */
    public Set<HeapEdge> getAllHeapEdges(final StatePosition realizedPosParam, final StatePosition suffix) {
        final LinkedList<StatePosition> todo = new LinkedList<>();
        final CollectionMap<StatePosition, NonRootPosition> seenCycles = new CollectionMap<>();
        final Collection<StatePosition> seenPositions = new LinkedHashSet<>();
        final Set<HeapEdge> edges = new LinkedHashSet<>();

        StatePosition realizedPos;
        if (suffix == null) {
            assert (realizedPosParam != null);
            // we traversed a cycle, but did not reach the start reference again
            // remove the cycle and continue normally
            final Pair<StatePosition, StatePosition> removedCycle = this.removeCycle(realizedPosParam, null);
            assert (removedCycle != null);
            for (final Iterator<StatePosition> it =
                realizedPosParam.getSuffixOf(removedCycle.x).getPathToRoot().descendingIterator(); it.hasNext();)
            {
                todo.add(it.next());
            }
            //todo.addAll(realizedPosParam.getSuffixOf(removedCycle.x).getPathFromRoot());
            realizedPos = removedCycle.x;
        } else {
            /*
             * Maybe we asked for a cycle traversal which can be traversed, but
             * does not reach the start again. In this case we have pos.cycle as
             * realized position, but want to consider pos as the realized
             * position and cycle.oldSuffix as the suffix that is not realized.
             */
            if (realizedPosParam != null) {
                assert (suffix instanceof NonRootPosition);
                final Pair<StatePosition, StatePosition> removedCycle = this.removeCycle(realizedPosParam, null);
                if (removedCycle != null) {
                    realizedPos = removedCycle.x;
                    final NonRootPosition continuation = realizedPosParam.getSuffixOf(realizedPos);
                    if (suffix.isPrefixOf(continuation)) {
                        for (final Iterator<StatePosition> it = continuation.getPathToRoot().descendingIterator(); it
                            .hasNext();)
                        {
                            todo.add(it.next());
                        }
                        //todo.addAll(continuation.getPathFromRoot());
                    } else {
                        for (final Iterator<StatePosition> it =
                            continuation.append((NonRootPosition) suffix).getPathToRoot().descendingIterator(); it
                            .hasNext();)
                        {
                            todo.add(it.next());
                        }
                        //todo.addAll(continuation.append((NonRootPosition) suffix).getPathFromRoot());
                    }

                } else {
                    realizedPos = realizedPosParam;
                    for (final Iterator<StatePosition> it = suffix.getPathToRoot().descendingIterator(); it.hasNext();)
                    {
                        todo.add(it.next());
                    }
                    //todo.addAll(suffix.getPathFromRoot());

                }
            } else {
                realizedPos = null;
                for (final Iterator<StatePosition> it = suffix.getPathToRoot().descendingIterator(); it.hasNext();) {
                    todo.add(it.next());
                }
                //todo.addAll(suffix.getPathFromRoot());
            }
        }

        while (!todo.isEmpty()) {
            final StatePosition currentSuffix = todo.pop();
            if (!seenPositions.add(currentSuffix)) {
                continue;
            }
            edges.addAll(currentSuffix.getHeapEdges());

            StatePosition current;
            if (currentSuffix instanceof NonRootPosition) {
                assert (realizedPos != null);
                current = realizedPos.append((NonRootPosition) currentSuffix);
            } else {
                current = currentSuffix;
            }

            StatePosition stripped;
            final Pair<StatePosition, StatePosition> removedCycle = this.removeCycle(current, null);
            if (removedCycle != null) {
                stripped = removedCycle.x;
            } else {
                stripped = current;
            }

            if (stripped.isPrefixOf(realizedPos)) {
                continue;
            }

            final Collection<NonRootPosition> continuations = this.cycleContinuations.get(stripped);
            if (continuations != null) {
                for (final NonRootPosition continuation : continuations) {
                    if (seenCycles.add(stripped, continuation)) {
                        for (final Iterator<StatePosition> it =
                            stripped.append(continuation).getSuffixOf(realizedPos).getPathToRoot().descendingIterator(); it
                            .hasNext();)
                        {
                            todo.add(it.next());
                        }
                        //todo.addAll(stripped.append(continuation).getSuffixOf(realizedPos).getPathFromRoot());
                    }
                }
            }
        }
        return edges;
    }

    /**
     * @param prefixResult information about what part of the position can be
     * reached
     * @return all heap edges that may be traversed by going along the
     * unrealized suffix from the prefix result in the state for which this
     * heapPos object was built. This includes all possible cycle runs!
     */
    public Set<HeapEdge> getAllHeapEdges(final PrefixResult prefixResult) {
        if (prefixResult.isRealized()) {
            return Collections.emptySet();
        }
        return this.getAllHeapEdges(prefixResult.getPosition(), prefixResult.getUnrealizedPosition());
    }

    /**
     * @param start a reference
     * @param end another reference
     * @return the edges that are on every path from start to end (which might help with cyclic annotations). The paths
     * may have a single abstract step at the end. Might return null if no path exists.
     */
    public Collection<HeapEdge> getAllNeededEdges(
        final AbstractVariableReference start,
        final AbstractVariableReference end)
    {
        final Pair<AbstractVariableReference, AbstractVariableReference> pair = new Pair<>(start, end);
        if (this.allNeededEdgesCache.containsKey(pair)) {
            final Collection<HeapEdge> result = this.allNeededEdgesCache.get(pair);
            return result;
        }
        Collection<HeapEdge> result = null;

        final Collection<AbstractVariableReference> endRefs = new LinkedHashSet<>();
        endRefs.add(end);
        for (final AbstractVariableReference partner : this.state
            .getHeapAnnotations()
            .getEqualityGraph()
            .getPartners(end))
        {
            endRefs.add(partner);
        }
        endRefs.addAll(this.state.getHeapAnnotations().getJoiningStructures().getReferencesWithPartner(end));

        for (final AbstractVariableReference endRef : endRefs) {
            for (final Collection<HeapEdge> coll : this.getNeededConnections(start, endRef, false)) {
                if (result == null) {
                    result = new LinkedHashSet<>(coll);
                } else {
                    result.retainAll(coll);
                }
            }
        }
        this.allNeededEdgesCache.put(pair, result);
        return result;
    }

    /**
     * @param pos some (root) state position
     * @return true if this heap contains this position
     */
    public boolean hasPosition(final StatePosition pos) {
        return this.posToRefCache.containsKey(pos);
    }
}
