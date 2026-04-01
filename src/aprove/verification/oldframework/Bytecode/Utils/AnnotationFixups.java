package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * When writing to memory (e.g. using PUTFIELD) we need to update the
 * annotations accordingly, because the write may also be seen from other
 * references. This whole process is implemented in this class.
 */
public final class AnnotationFixups {
    /**
     * Do not create me.
     */
    private AnnotationFixups() {

    }

    /**
     * Add annotations needed to keep our state representation valid after
     * explicitly adding a new connection for a concrete, existing
     * non-primitive. This is done for the PUTFIELD and AASTORE opcodes.
     * @param state State in which a write access connecting <code>parentRef
     *  </code> and <code>childRef</code> will occur <em>after</em> calling this
     * method.
     * @param parentRef abstract variable reference to the reference type value
     * written to.
     * @param newConnection the connection between <code>parentRef</code> and
     * <code>childRef</code> which is about to be created.
     * @param childRef abstract variable reference to the value that is written.
     * @param cloneAfterWrite a clone of state where the write was performed
     * already (for abstract connections it suffices to give state without
     * cloning)
     * @param concreteWrite true iff we write to some concrete, realized
     * instance (false: into abstract object/array)
     * @return information about changes in Defreach annotations that _must_ be regarded
     */
    public static Collection<DefiniteReachabilityAnnotationCreation> annotateAsNewConcreteChild(
        final State state,
        final AbstractVariableReference parentRef,
        final HeapEdge newConnection,
        final AbstractVariableReference childRef,
        final State cloneAfterWrite,
        final boolean concreteWrite)
    {
        // x \sim y iff x =?= y or x -><- y
        // x \rightsquigarrow y iff x.f1.f2....fn=z and z \sim y (n \ge 0 allowing for x=z)
        assert (state != null);
        assert (parentRef != null);
        assert (childRef != null);
        if (!childRef.pointsToReferenceType()) {
            // nothing to do here
            return Collections.emptySet();
        }

        final HeapAnnotations annotations = state.getHeapAnnotations();
        final HeapPositions heapPos = new HeapPositions(state.clone());

        if (childRef.isNULLRef()) {
            /*
             * Well, if the written instance has only one ref field
             * and that is null, we can remove all kinds of annotations!
             */
            final AbstractType parentType = annotations.getAbstractType(parentRef);
            final boolean parentHasOnlyOneRefField = state.getClassPath().typeHasOnlyOneRefField(parentType, state.getJBCOptions());
            if (parentHasOnlyOneRefField) {
                annotations.getCyclicStructures().remove(parentRef);
                annotations.getPossiblyNonTreeRefs().remove(parentRef);
            }

            return Collections.emptySet();
        }

        final LinkedHashSet<AbstractVariableReference> possiblyNonTreeOld =
            new LinkedHashSet<>(annotations.getPossiblyNonTreeRefs());
        final JoiningStructures joiningStructuresOld = annotations.getJoiningStructures().clone();
        final EqualityGraph eqGraph = annotations.getEqualityGraph();
        final CyclicStructures cyclicStructuresOld = annotations.getCyclicStructures().clone();
        final JoiningStructures joiningStructuresNew = annotations.getJoiningStructures();
        final CyclicStructures cyclicStructuresNew = annotations.getCyclicStructures();

        /*
         * If the parent is abstract, then we treat it as if it was a predecessor of itself. In this way, it gets all
         * required annotations.
         */
        final AbstractVariable parentVar = state.getAbstractVariable(parentRef);
        final boolean parentIsAbstract = parentVar instanceof AbstractInstance || parentVar instanceof AbstractArray;
        final Collection<Pair<AbstractVariableReference, Boolean>> abstractedPreds =
            AnnotationFixups.getSim(parentRef, parentIsAbstract, eqGraph, joiningStructuresOld);

        final Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> rightSquigPair =
            AnnotationFixups.getRightSquigArrow(childRef, true, heapPos.getState());
        final Collection<AbstractVariableReference> concreteSuccs = rightSquigPair.x;
        final Collection<AbstractVariableReference> refsConcretelyReachableFromChild = concreteSuccs;
        final Collection<AbstractVariableReference> abstractedSuccs = rightSquigPair.y;

        final Collection<StatePosition> childPositions = heapPos.getPositionsForRef(childRef);

        final boolean parentReachesChild = Reachability.getReachableRefs(parentRef, false, state).contains(childRef);

        if (!parentReachesChild) {
            /*
             * If there are two connections from child to q, we now also have
             * (these) two connections from parent to q. If there was a
             * connection from parent to child before, no new connection is
             * visible and nothing needs to be done.
             */
            /*
             * parent.f = child
             * p \sim parent
             * child -x-> q
             * child -y-> q
             * x != y
             * ---------------------------------------------------------------------
             * mark p with cyclic/non-tree
             */
            final CollectionMap<AbstractVariableReference, StatePosition> refsWithMultiplePositions =
                heapPos.getRefsWithMultiplePositions();
            refsWithMultiplePositions.keySet().retainAll(refsConcretelyReachableFromChild);

            /*
             * We now have references which are both reachable using at least two
             * positions and reachable from childRef. We need those which are
             * reachable by at least two positions, where both of these also go
             * through childRef.
             */
            for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> entry : refsWithMultiplePositions
                .entrySet())
            {
                for (final Pair<StatePosition, StatePosition> pair : Collection_Util.getPairs(entry.getValue())) {
                    final StatePosition posA = pair.x;
                    final StatePosition posB = pair.y;
                    for (final StatePosition childPos : childPositions) {
                        if (childPos.isPrefixOf(posA) && childPos.isPrefixOf(posB)) {
                            // non-tree!

                            // cycle?
                            Collection<HeapEdge> neededEdges = null;
                            if (posA.isPrefixOf(posB)) {
                                neededEdges = posB.getEdgesTo(posA);
                            } else if (posB.isPrefixOf(posA)) {
                                neededEdges = posA.getEdgesTo(posB);
                            }
                            for (final Pair<AbstractVariableReference, Boolean> p : abstractedPreds) {
                                final AbstractVariableReference r = p.x;
                                if (neededEdges != null || HeapAnnotations.canBeNonTree(r, state)) {
                                    annotations.setPossiblyNonTree(r);
                                }
                                if (neededEdges != null) {
                                    annotations.setPossiblyCyclic(r, neededEdges);
                                }
                            }
                        }
                    }
                }
            }

            P_LOOP: for (final Pair<AbstractVariableReference, Boolean> p : abstractedPreds) {
                final AbstractVariableReference abstrPred = p.x;
                /*
                 * parent.f = child
                 * p \sim parent
                 * child --> childSucc
                 * childSucc non-tree
                 * -----------------------------------------------------------------
                 * p non-tree
                 * if childSucc is marked as possibly-cyclic with information m',
                 * then p is marked as possibly-cyclic with the intersection of m'
                 * and, if it exists, the old possibly-cyclic information of p
                 */
                for (final AbstractVariableReference childSucc : refsConcretelyReachableFromChild) {
                    if (possiblyNonTreeOld.contains(childSucc) && HeapAnnotations.canBeNonTree(abstrPred, state)) {
                        annotations.setPossiblyNonTree(abstrPred);
                    }
                    if (cyclicStructuresOld.isCyclic(childSucc)) {
                        annotations.setPossiblyNonTree(abstrPred);
                        annotations.setPossiblyCyclic(abstrPred, cyclicStructuresOld.getNeededEdgesOf(childSucc));
                        if (cyclicStructuresNew.getNeededEdgesOf(abstrPred).isEmpty()) {
                            // nothing to change for this p anymore
                            continue P_LOOP;
                        }
                    }
                }
            }
        }

        for (final Pair<AbstractVariableReference, Boolean> p : abstractedPreds) {
            final AbstractVariableReference abstrPred = p.x;
            /*
             * parent.f = child
             * p \sim parent
             * child \rightsquigarrow q
             * -----------------------------------------------------------------
             * p \joins q
             */
            /*
             * TODO Do not add p \joins q if there already is p \joins child?
             * Consider p \joins parent and parent \joins q. Now write
             * parent.f = parent. Why do we introduce p \joins q then?
             */
            for (final AbstractVariableReference q : concreteSuccs) {
                joiningStructuresNew.add(abstrPred, q);
            }
            for (final AbstractVariableReference q : abstractedSuccs) {
                joiningStructuresNew.add(abstrPred, q);
            }
        }

        /*
         * parent.f = child
         * p \rightsquigarrow(x) parent
         * child \rightsquigarrow(z) q
         * p \rightsquigarrow(y) q
         * x, y do not have a common prefix
         * ---------------------------------------------------------------------
         * p non-tree
         * if y is epsilon: p non-tree and possibly-cyclic with m as follows:
         *  m is the intersection of ({f}, the fields in x, the fields in
         *  z) and the old possibly-cyclic information m'
         */

        /*
         * We construct a map from the predecessors p of parent to a set of
         * pairs of values describing the connection. The first pair element
         * determines if the connection between p and parent is concrete.
         * The second part contains the concrete connection.
         */
        final CollectionMap<AbstractVariableReference, Pair<Boolean, NonRootPosition>> parentPredecessors =
            AnnotationFixups.computeParentPredecessors(parentRef, abstractedPreds, heapPos);

        final NonRootPosition nrp = newConnection.getNonRootPosition();
        Collection<AbstractVariableReference> concreteOldChildSuccessors = Collections.emptySet();
        final AbstractVariableReference oldChild;
        if (nrp != null) {
            oldChild = nrp.getFromState(parentRef, state);
            if (oldChild != null) {
                concreteOldChildSuccessors = AnnotationFixups.getRightSquigArrow(oldChild, true, heapPos.getState()).x;
            }
        } else {
            oldChild = null;
        }

        final Collection<AbstractVariableReference> concreteChildSuccessorsSimParent = new LinkedHashSet<>();
        for (final Pair<AbstractVariableReference, Boolean> abstractPair : abstractedPreds) {
            concreteChildSuccessorsSimParent.add(abstractPair.x);
        }
        concreteChildSuccessorsSimParent.retainAll(refsConcretelyReachableFromChild);

        // all references that are reachable from childRef
        final Collection<AbstractVariableReference> childSuccessors = new LinkedHashSet<>();
        childSuccessors.addAll(refsConcretelyReachableFromChild);
        childSuccessors.addAll(abstractedSuccs);

        /*
         * Now for all reachable children, we check if it is one of the
         * predecessor (in that case, we have a cycle) or if it can be reached
         * by one one of the predecessors (in that case, we have a acyclic
         * non-tree shape):
         */
        for (final AbstractVariableReference childSuccessorRef : childSuccessors) {
            final boolean onlyConcretePathsFromChildToChildSucc = !abstractedSuccs.contains(childSuccessorRef);
            final boolean concretePathFromChildToChildSuccPossible =
                refsConcretelyReachableFromChild.contains(childSuccessorRef);
            final Collection<Pair<AbstractVariableReference, Boolean>> abstractChildSuccPredecessors =
                AnnotationFixups.getSim(childSuccessorRef, true, eqGraph, joiningStructuresOld);

            for (final Pair<AbstractVariableReference, Boolean> childSuccessorSimPredInfo : abstractChildSuccPredecessors)
            {
                final AbstractVariableReference abstractChildSuccPredRef = childSuccessorSimPredInfo.x;

                final boolean childSuccPredToChildSuccConcrete =
                    abstractChildSuccPredRef.equals(childSuccessorRef) && !childSuccessorSimPredInfo.y.booleanValue();

                /*
                 * Now check the concrete position of these (abstract)
                 * predecessors and see if we find a reference that we
                 * know from the parent set:
                 */
                for (final StatePosition childSuccessorSimPredPos : heapPos
                    .getPositionsForRef(abstractChildSuccPredRef))
                {
                    for (final Entry<AbstractVariableReference, Collection<Pair<Boolean, NonRootPosition>>> parentPredInfo : parentPredecessors
                        .entrySet())
                    {
                        final AbstractVariableReference parentPredRef = parentPredInfo.getKey();

                        for (final StatePosition parentPredPos : heapPos.getPositionsForRef(parentPredRef)) {
                            /*
                             * If parentPredRef is a (concrete) predecessor of
                             * abstractChildSuccPredRef, there is a pair of
                             * positions of these two such that parentPredPos is
                             * a prefix of childSuccessorSimPredPos:
                             */
                            if (!parentPredPos.isPrefixOf(childSuccessorSimPredPos)) {
                                /*
                                 * It is not possible to go from parentPred to
                                 * childSuccessorSimPred, but this is the
                                 * connection we are looking for.
                                 */
                                continue;
                            }
                            final NonRootPosition pathFromParentPredToChildSuccPred =
                                childSuccessorSimPredPos.getSuffixOf(parentPredPos);

                            /*
                             * Now we check each of the connections from
                             * parentPred to parent to see what annotations
                             * we need:
                             */
                            for (final Pair<Boolean, NonRootPosition> t : parentPredInfo.getValue()) {
                                final boolean parentPredToParentConcrete = t.x.booleanValue();
                                final NonRootPosition pathFromParentPredToParent = t.y;
                                if (pathFromParentPredToParent != null && pathFromParentPredToChildSuccPred != null) {
                                    final StatePosition commonPrefix =
                                        pathFromParentPredToParent
                                            .getMaxCommonPrefix(pathFromParentPredToChildSuccPred);
                                    /*
                                     * If both paths have a common prefix,
                                     * this is not the bottommost reference
                                     * before both references are reached.
                                     * As example, consider
                                     *                   ,-g-- parent              child
                                     * parentPred --f-- r                            |
                                     *                   '-h-- childSuccPred -><- childSucc
                                     * Here, the path
                                     *  from parentPred to parent is fg and
                                     *  from parentPred to childSuccPred is fh
                                     * Thus, the prefix is non-empty, as an
                                     * annotation needs to be done on r,
                                     * not on parentPred.
                                     */
                                    if (commonPrefix != null) {
                                        continue;
                                    }
                                }

                                // from the parent predecessor we reach the parent without the need for =?= or -><-
                                final boolean allConcrete =
                                    parentPredToParentConcrete
                                        && childSuccPredToChildSuccConcrete
                                        && onlyConcretePathsFromChildToChildSucc
                                        && concreteWrite;

                                //If all of the connections are concrete, we don't need no annotation.
                                if (allConcrete) {
                                    continue;
                                }

                                if (!annotations.isPossiblyNonTree(parentPredRef)
                                    && concreteOldChildSuccessors.contains(childSuccessorRef))
                                {
                                    continue;
                                }

                                if (HeapAnnotations.canBeNonTree(parentPredRef, state)) {
                                    // we will add non-tree below if we detect a cycle
                                    annotations.setPossiblyNonTree(parentPredRef);
                                }

                                if (!annotations.getCyclicStructures().isCyclic(parentPredRef)
                                    && concreteOldChildSuccessors.contains(childSuccessorRef))
                                {
                                    continue;
                                }

                                if (!concreteOldChildSuccessors.isEmpty()
                                    && concreteChildSuccessorsSimParent.containsAll(concreteOldChildSuccessors))
                                {
                                    continue;
                                }

                                /*
                                 * Is there a cycle? If so, do we really
                                 * need to add an annotation for
                                 * parentPredRef?
                                 */
                                if (pathFromParentPredToChildSuccPred != null) {
                                    // no cycle
                                    continue;
                                }

                                assert (parentPredRef.equals(abstractChildSuccPredRef));

                                /*
                                 * The following optimizations find cases where we essentially would exploit transitive
                                 * joins annotations, which we do not have.
                                 *
                                 * In the case where a connection spanning three references (a - b - c) is chosen using
                                 * only abstract connections, we are free to not add the "cyclic" annotation if (and
                                 * this is important!) no direct annotation (a - c) exists.
                                 *
                                 * Note: There may be other loop iterations for the connections so that we do not skip
                                 * the creation of a cyclic annotation!
                                 */

                                final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> check =
                                    new LinkedHashSet<>();
                                if (!childSuccPredToChildSuccConcrete) {
                                    assert (!abstractChildSuccPredRef.equals(childSuccessorRef) || joiningStructuresOld
                                        .areJoining(childSuccessorRef, childSuccessorRef));
                                    assert (eqGraph.areMarkedAsPossiblyEqual(
                                        abstractChildSuccPredRef,
                                        childSuccessorRef) || joiningStructuresOld.areJoining(
                                        abstractChildSuccPredRef,
                                        childSuccessorRef));
                                    /*
                                     * We have an abstract connection from parentPred=childSuccPred to childSucc. If one
                                     * of the other connections is also abstract, we do not need to introduce the cyclic
                                     * annotation if the corresponding connection is not allowed by another annotation.
                                     */
                                    if (!parentPredToParentConcrete && !concretePathFromChildToChildSuccPossible) {
                                        /*
                                         * abstract: child - childSucc - parentPred - parent
                                         *
                                         * We now need to allow the following connections using annotations:
                                         *  1) child - parentPred
                                         *  2) child - parent
                                         *  3) childSucc - parent
                                         */
                                        check.add(new Pair<>(childRef, parentPredRef));
                                        check.add(new Pair<>(childRef, parentRef));
                                        check.add(new Pair<>(childSuccessorRef, parentRef));
                                    } else if (!parentPredToParentConcrete) {
                                        /*
                                         * (maybe) concrete: child - childSucc
                                         * abstract: childSucc - parentPred - parent
                                         *
                                         * We now need to have childSucc - parent using some annotation.
                                         */
                                        check.add(new Pair<>(childSuccessorRef, parentRef));
                                    } else if (!concretePathFromChildToChildSuccPossible) {
                                        /*
                                         * concrete: parentPred - parent
                                         * abstract: child - childSucc - parentPred
                                         *
                                         * We now need to have child - parentPred using some annotation.
                                         */
                                        check.add(new Pair<>(childRef, parentPredRef));
                                    }
                                } else {
                                    assert (childSuccessorRef.equals(abstractChildSuccPredRef));
                                    // parentPred=childSuccPred=childSucc

                                    /*
                                     * If we now have an abstract connection between parentPred and parent and another
                                     * abstract connection between child and childSucc=parentPred, we do not need to add
                                     * a cyclic annotation if the connection from parent and child is not allowed by a
                                     * (non-transitive) annotation.
                                     *
                                     * Without explicitly checking for this annotation, not adding "cyclic" is wrong!
                                     */
                                    if (!parentPredToParentConcrete && !concretePathFromChildToChildSuccPossible) {
                                        check.add(new Pair<>(childRef, parentRef));
                                    }
                                }

                                boolean doNotAdd = false;
                                for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : check) {
                                    final AbstractVariableReference refA = pair.x;
                                    final AbstractVariableReference refB = pair.y;
                                    if (!joiningStructuresOld.areJoining(refA, refB)
                                        && !eqGraph.areMarkedAsPossiblyEqual(refA, refB)
                                        && !refA.equals(refB))
                                    {
                                        // TODO is it OK to check for less?
                                        doNotAdd = true;
                                        break;
                                    }
                                }
                                if (doNotAdd) {
                                    continue;
                                }

                                if (parentReachesChild && !cyclicStructuresOld.isCyclic(parentPredRef)) {
                                    // it was acylic before, so it still is acyclic
                                    continue;
                                }

                                //Check if we can actually reach the parent by looking at the reachable type set:
                                final AbstractType parentRefType = state.getAbstractType(parentRef);
                                final AbstractType parentPredReachableTypes =
                                    annotations.getReachableTypes(parentPredRef);
                                if (!parentRefType.hasIntersectionWith(parentPredReachableTypes, state.getClassPath(), state.getJBCOptions()))
                                {
                                    continue;
                                }

                                final Collection<HeapEdge> neededEdges = new LinkedHashSet<>();
                                if (pathFromParentPredToParent != null) {
                                    neededEdges.addAll(StatePosition.getHeapEdges(pathFromParentPredToParent));
                                }
                                if (newConnection != UnknownArrayMemberEdge.INSTANCE) {
                                    neededEdges.add(newConnection);
                                }
                                final Collection<HeapEdge> neededEdgesFromChildToChildSucc =
                                    heapPos.getAllNeededEdges(childRef, childSuccessorRef);
                                if (neededEdgesFromChildToChildSucc != null
                                    && !neededEdgesFromChildToChildSucc.isEmpty())
                                {
                                    neededEdges.addAll(neededEdgesFromChildToChildSucc);
                                }

                                annotations.setPossiblyNonTree(parentRef);
                                annotations.setPossiblyCyclic(parentRef, neededEdges);
                                annotations.setPossiblyNonTree(childRef);
                                annotations.setPossiblyCyclic(childRef, neededEdges);
                                annotations.setPossiblyNonTree(childSuccessorRef);
                                annotations.setPossiblyCyclic(childSuccessorRef, neededEdges);
                                annotations.setPossiblyNonTree(parentPredRef);
                                annotations.setPossiblyCyclic(parentPredRef, neededEdges);
                            }
                        }
                    }
                }
            }
        }

        AnnotationFixups.removeAnnotationsIntroducingForbiddenShapes(state, cloneAfterWrite);
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach =
            AnnotationFixups.removeAnnotationsThatMightHaveBeenBroken(state, parentRef, newConnection, oldChild, childRef);

        AnnotationFixups.addNewlyReachableTypes(state, parentRef, childRef);

        return newDefReach;
    }

    /**
     * Update the reachable type information for abstract predecessors of the
     * written reference.
     * @param state State in which a write access connecting <code>parentRef
     *  </code> and <code>childRef</code> will occur <em>after</em> calling this
     * method.
     * @param parentRef abstract variable reference to the reference type value
     * written to.
     * @param childRef the new value for the written field
     */
    private static void addNewlyReachableTypes(
        final State state,
        final AbstractVariableReference parentRef,
        final AbstractVariableReference childRef)
    {
        final ClassPath cPath = state.getClassPath();
        final HeapAnnotations heapAnns = state.getHeapAnnotations();
        final Collection<AbstractVariableReference> abstrPreds =
            heapAnns.getJoiningStructures().getReferencesWithPartner(parentRef);
        abstrPreds.add(parentRef);

        //Find all reachable types:
        final Collection<AbstractVariableReference> reachableRefs =
            Reachability.getReachableRefs(childRef, false, state);
        reachableRefs.add(childRef);
        final List<AbstractType> reachableTypes = new LinkedList<>();
        for (final AbstractVariableReference reachedRef : reachableRefs) {
            reachableTypes.add(heapAnns.getAbstractType(reachedRef));
            reachableTypes.add(heapAnns.getReachableTypes(reachedRef));
        }
        final AbstractType newlyReachableTypes = AbstractType.union(cPath, state.getJBCOptions(), reachableTypes);

        //Inform new abstract predecessors about the newly reachable types
        for (final AbstractVariableReference abstrPredRef : abstrPreds) {
            heapAnns.addReachableTypes(abstrPredRef, newlyReachableTypes, cPath, state.getJBCOptions());
        }
    }

    /**
     * Removes -F!-> annotations that might be broken by a write access.
     * @param state State in which a write access connecting <code>parentRef
     *  </code> and <code>childRef</code> will occur <em>after</em> calling this
     * method.
     * @param parentRef abstract variable reference to the reference type value
     * written to.
     * @param newConnection the connection between <code>parentRef</code> and
     * <code>childRef</code> which is about to be created.
     * @param oldChildRef the old value for the written field
     * @param newChildRef the new value for the written field
     * @return information about changes in Defreach annotations that _must_ be regarded
     */
    private static Collection<DefiniteReachabilityAnnotationCreation> removeAnnotationsThatMightHaveBeenBroken(
        final State state,
        final AbstractVariableReference parentRef,
        final HeapEdge newConnection,
        final AbstractVariableReference oldChildRef,
        final AbstractVariableReference newChildRef)
    {
        final HeapAnnotations heapAnns = state.getHeapAnnotations();

        final DefiniteReachabilities dras = heapAnns.getDefiniteReachabilities();
        final List<DefiniteReachabilityAnnotation> toRemove = new LinkedList<>();

        /*
         * Find o -><- parent with o -F!-> o' and newConnection \in F, then remove those.
         *
         * However, if the path described by the overwritten field is also possible in the state after writing the
         * connection, defreach annotations may be retained.
         *
         * Example:
         * State before: a.f=b and c.f=b
         * Writing: a.f=c
         * State after: a.f=c and c.f=b
         *
         * The annotation b -{f}!!-> b may be retained because the old path through a is deleted, but a new path through
         * a and c is now possible. However, we need to take care that the length of the path described by the
         * annotation is now different.
         *
         * Another optimization:
         * State before: a.f=b, b.f=c, c -+><+- a, c -{n}!-> d
         * Writing: a.f=c
         * State after: a.f=c
         *
         * Without the optimization, we think that writing to a (which might be a successor of c) could destroy the path
         * from c to d described by c -{n}!-> d. However, we know that after the write access only the reference b is
         * not reachable anymore, meaning only a part of the path from c to d could have been deleted and the annotation
         * can be retained.
         *
         * We may retain the annotation if:
         *  - for each reference x that was reachable before, but is not anymore after the write access:
         *   - x is not the target of the definite reachability annotation, and
         *   - all fields of the annotation are realized in x
         *
         * With this we can detect that we a) removed the DefReach target or b) we removed a reference that leads to the
         * DefReach target using some abstract successor.
         */

        // is it possible to reach the old field target from the new target?
        final AbstractVariableReference reachedRef =
            Reachability.followFields(newChildRef, Collections.singleton(newConnection), oldChildRef, true, state);

        boolean optimizationLongerPath;
        if (oldChildRef != null && oldChildRef.equals(reachedRef)) {
            /*
             * We can retain the annotation, but need to update its length. The path described after the write access
             * could be the same, but could also be longer (namely the old length + the length of the path from
             * parentRef to oldChildRef over newChildRef)
             */
            optimizationLongerPath = true;
        } else {
            optimizationLongerPath = false;
        }

        final Collection<DefiniteReachabilityAnnotation> optimizationShorterPath = new LinkedHashSet<>();

        final Collection<AbstractVariableReference> joiningRefs =
            heapAnns.getJoiningStructures().getReferencesWithPartner(parentRef);
        for (final AbstractVariableReference joiningRef : joiningRefs) {
            for (final DefiniteReachabilityAnnotation dra : dras) {
                if (dra.getFrom().equals(joiningRef)
                    && !dra.getTo().equals(parentRef)
                    && dra.getFields().contains(newConnection))
                {
                    /*
                     * We want to exclude some special cases here.
                     * For example, if we have
                     *  joiningRef -!!-> joiningRef
                     * then this connection is only broken if parentRef is
                     * on the cycle between joiningRef and joiningRef.
                     * Hence, the old field value of parentRef would also
                     * need to reach parentRef.
                     */
                    if (dra.getFrom().equals(dra.getTo()) && dra.getFields().contains(newConnection)) {
                        if (!heapAnns.getJoiningStructures().areJoining(oldChildRef, parentRef)) {
                            continue;
                        }
                    }

                    // try to detect the case described as the second optimization above
                    final Collection<AbstractVariableReference> reachableBefore =
                        Reachability.followFields(parentRef, dra.getFields(), state);

                    /*
                     * Compute the references that are reachable starting in newChildRef, but without going through
                     * parentRef (which still has the old field value in state)
                     */
                    final Collection<AbstractVariableReference> reachableAfter = new LinkedHashSet<>();
                    Reachability.followFields(newChildRef, dra.getFields(), reachableAfter, parentRef, false, state);
                    reachableAfter.add(parentRef);

                    final Collection<AbstractVariableReference> notReachableAnymore =
                        new LinkedHashSet<>(reachableBefore);
                    notReachableAnymore.removeAll(reachableAfter);

                    boolean optimize = true;
                    for (final AbstractVariableReference removed : notReachableAnymore) {
                        if (removed.equals(dra.getTo())) {
                            optimize = false;
                            break;
                        }
                        final AbstractVariable var = state.getAbstractVariable(removed);
                        if (!(var instanceof ConcreteInstance)) {
                            optimize = false;
                            break;
                        }
                        final ConcreteInstance ci = (ConcreteInstance) var;
                        boolean foundField = false;
                        for (final HeapEdge fieldHeapEdge : dra.getFields()) {
                            if (!(fieldHeapEdge instanceof InstanceFieldEdge)) {
                                break;
                            }
                            final FieldIdentifier id = ((InstanceFieldEdge) fieldHeapEdge).getFieldIdentifier();
                            final AbstractVariableReference fieldContent =
                                ci.getField(id.getClassName(), id.getFieldName(), true);
                            if (fieldContent != null) {
                                foundField = true;
                                break;
                            }
                        }
                        if (!foundField) {
                            optimize = false;
                            break;
                        }
                    }

                    if (optimize) {
                        optimizationShorterPath.add(dra);
                    } else {
                        toRemove.add(dra);
                    }
                }
            }
        }

        if (optimizationLongerPath) {
            final LinkedHashSet<DefiniteReachabilityAnnotationCreation> res = new LinkedHashSet<>();
            for (final DefiniteReachabilityAnnotation defReach : toRemove) {
                res.add(new DefiniteReachabilityAnnotationCreation(defReach, defReach, IntegerRelationType.GE));
            }
            return res;
        }

        final LinkedHashSet<DefiniteReachabilityAnnotationCreation> res = new LinkedHashSet<>();
        for (final DefiniteReachabilityAnnotation defReach : optimizationShorterPath) {
            res.add(new DefiniteReachabilityAnnotationCreation(defReach, defReach, IntegerRelationType.LE));
        }
        dras.removeAll(toRemove);
        return res;
    }

    /**
     * <p>
     * Remove annotations that would only generate shapes which are forbidden.
     * Imagine x->y->z with x joins z. When now making use of the joins
     * annotation, we would create a forbidden non-tree/cyclic shape.
     * </p>
     * <p>
     * Conditions:
     * <ol>
     * <li>x -+><+- z or x =?= z</li>
     * <li>x is acyclic</li>
     * <li>x is not marked with non-tree or we are dealing with =?= or x is
     * fully realized</li>
     * <li>x reaches z using concrete connections</li>
     * </ol>
     */
    private static void removeAnnotationsIntroducingForbiddenShapes(final State state, final State cloneAfterWrite) {
        final HeapAnnotations annotations = state.getHeapAnnotations();
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> removeEq = new LinkedHashSet<>();
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> removeJoins =
            new LinkedHashSet<>();
        final CollectionMap<AbstractVariableReference, Pair<AbstractVariableReference, Boolean>> todo =
            new CollectionMap<>();
        for (final TwoRefs twoRefs : annotations.getJoiningStructures().getJoinsAnnotations()) {
            todo.add(twoRefs.getRefOne(), new Pair<>(twoRefs.getRefTwo(), Boolean.TRUE));
            todo.add(twoRefs.getRefTwo(), new Pair<>(twoRefs.getRefOne(), Boolean.TRUE));
        }

        for (final AbstractVariableReference x : annotations.getEqualityGraph().getReferences()) {
            for (final AbstractVariableReference z : annotations.getEqualityGraph().getPartners(x)) {
                todo.add(x, new Pair<>(z, Boolean.FALSE));
            }
        }

        for (final Entry<AbstractVariableReference, Collection<Pair<AbstractVariableReference, Boolean>>> entry : todo
            .entrySet())
        {
            final AbstractVariableReference x = entry.getKey();
            if (annotations.getCyclicStructures().isCyclic(x)) {
                continue;
            }
            final Collection<AbstractVariableReference> reachable =
                Reachability.getReachableRefs(x, false, cloneAfterWrite);

            for (final Pair<AbstractVariableReference, Boolean> pair : entry.getValue()) {
                final boolean joins = pair.y;
                /*
                 * For x joins z we'd like to see that the annotation only expresses a connection from z back to x
                 * introducing a cycle. For this x must be fully realized.
                 *
                 * If x is not fully realized, the annotation may mean another connection from x to z (in addition to
                 * the one that already exists using concrete connections). In this case, we have a non-tree shape.
                 */
                if (joins && annotations.isPossiblyNonTree(x) && !state.isFullyRealized(x)) {
                    continue;
                }

                final AbstractVariableReference z = pair.x;
                if (reachable.contains(z)) {
                    if (joins) {
                        removeJoins.add(new Pair<>(x, z));
                    } else {
                        removeEq.add(new Pair<>(x, z));
                    }
                }
            }
        }

        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : removeEq) {
            annotations.getEqualityGraph().remove(pair.x, pair.y);
        }

        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : removeJoins) {
            annotations.getJoiningStructures().remove(pair.x, pair.y);
        }
    }

    /**
     * Compute the predecessors of parentRef.
     * @param parentRef the reference for which we need the predecessors
     * @param abstractedPreds the \sim-predecessors of parentRef
     * @param heapPos the heap positions of this state
     * @return the predecessors of the parent reference. For each predecessor
     * and each path leading from it to the parent reference, we store a) if the
     * connection is concrete b) the path itself for the concrete part of the
     * path
     */
    private static CollectionMap<AbstractVariableReference, Pair<Boolean, NonRootPosition>> computeParentPredecessors(
        final AbstractVariableReference parentRef,
        final Collection<Pair<AbstractVariableReference, Boolean>> abstractedPreds,
        final HeapPositions heapPos)
    {
        final CollectionMap<AbstractVariableReference, Pair<Boolean, NonRootPosition>> parentPredecessors =
            new CollectionMap<>();

        //Add parentRef itself:
        parentPredecessors.add(parentRef, new Pair<>(Boolean.TRUE, (NonRootPosition) null));

        //Add all abstract predecessors of parentRef:
        for (final Pair<AbstractVariableReference, Boolean> p : abstractedPreds) {
            parentPredecessors.add(p.x, new Pair<>(Boolean.FALSE, (NonRootPosition) null));
        }

        /*
         * Add all concrete predecessors of the entries in parentPredecessors
         * (into the temporary toAdd, then into parentPredecessors to avoid
         * the concurrent modification):
         */
        final Collection<Pair<AbstractVariableReference, Pair<Boolean, NonRootPosition>>> toAdd = new LinkedList<>();
        for (final Map.Entry<AbstractVariableReference, Collection<Pair<Boolean, NonRootPosition>>> e : parentPredecessors
            .entrySet())
        {
            final AbstractVariableReference ref = e.getKey();
            for (final Pair<Boolean, NonRootPosition> con : e.getValue()) {
                final Boolean isConcreteConnection = con.x;
                for (final Entry<AbstractVariableReference, Collection<NonRootPosition>> predInfo : AnnotationFixups.getAllPredecessors(
                    ref,
                    heapPos).entrySet())
                {
                    final AbstractVariableReference predRef = predInfo.getKey();
                    for (final NonRootPosition concrPath : predInfo.getValue()) {
                        toAdd.add(new Pair<>(predRef, new Pair<>(isConcreteConnection, concrPath)));
                    }
                }
            }
        }

        for (final Pair<AbstractVariableReference, Pair<Boolean, NonRootPosition>> t : toAdd) {
            parentPredecessors.add(t.x, t.y);
        }

        return parentPredecessors;
    }

    /**
     * @param ref some reference
     * @param state the state to work on
     * @return a pair of collections of references, where the first pair
     * component gives all references which are reachable from ref using only
     * realized parts on the heap. The second component contains the references
     * which can be reached by furthermore using a single connection using one
     * of the annotations "possible equality" or "joins". Thus, when calling the
     * method for ref = x in a heap with x.f=y, y =?= z and y -><- u the first
     * collection contains x and y and the second collection contains z and u.
     */
    public static Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> getRightSquigArrow(
        final AbstractVariableReference ref, boolean includeSelf, final State state)
    {
        final Set<AbstractVariableReference> concretelyReachableRefs = new LinkedHashSet<>();
        final Set<AbstractVariableReference> abstractlyReachableRefs = new LinkedHashSet<>();
        final Pair<Set<AbstractVariableReference>, Set<AbstractVariableReference>> result =
                new Pair<>(concretelyReachableRefs, abstractlyReachableRefs);
        if (ref.isNULLRef()) {
            return result;
        }

        // The reference itself is reachable
        if (includeSelf) {
            concretelyReachableRefs.add(ref);
        }

        /*
         * TODO in case all (!) possible connections can be computed, it might
         * make sense to look at these individually in order to get a more
         * precise information for the possibly-cyclic-annotation.
         */
        concretelyReachableRefs.addAll(Reachability.getReachableRefs(ref, false, state));

        final EqualityGraph eqGraph = state.getHeapAnnotations().getEqualityGraph();
        final JoiningStructures joiningStructures = state.getHeapAnnotations().getJoiningStructures();

        for (final AbstractVariableReference concrReachRef : concretelyReachableRefs) {
            final Collection<Pair<AbstractVariableReference, Boolean>> sims =
                AnnotationFixups.getSim(concrReachRef, false, eqGraph, joiningStructures);

            for (final Pair<AbstractVariableReference, Boolean> simPair : sims) {
                // Add the edges leading to the reachable refs:
                abstractlyReachableRefs.add(simPair.x);
            }
        }
        return result;
    }

    /**
     * @param ref a reference
     * @param heapPos information about the heap
     * @return a collection of all references that can concretely reach <code>
     *  ref</code>, together with a collection of edges used for this concrete
     * connection (all possible connections where each cycle is at most
     * traversed once).
     */
    public static CollectionMap<AbstractVariableReference, NonRootPosition> getAllPredecessors(
        final AbstractVariableReference ref,
        final HeapPositions heapPos)
    {
        final CollectionMap<AbstractVariableReference, NonRootPosition> result = new CollectionMap<>();

        final State state = heapPos.getState();

        final LinkedList<Pair<StatePosition, NonRootPosition>> todo = new LinkedList<>();
        final Collection<StatePosition> seen = new LinkedHashSet<>();
        for (final StatePosition pos : heapPos.getPositionsForRef(ref)) {
            todo.add(new Pair<StatePosition, NonRootPosition>(pos, null));
        }
        while (!todo.isEmpty()) {
            final Pair<StatePosition, NonRootPosition> pair = todo.pop();
            final StatePosition pos = pair.x;
            final NonRootPosition suffix = pair.y;
            if (pos == null) {
                continue;
            }
            if (!seen.add(pos)) {
                continue;
            }

            final AbstractVariableReference predRef = state.getReference(pos);
            result.add(predRef, suffix);

            // now look at the predecessor(s)
            if (pos instanceof NonRootPosition) {
                final NonRootPosition nrp = (NonRootPosition) pos;
                todo.add(new Pair<>(nrp.getPrev(), (NonRootPosition) nrp.getSuffixOf(nrp.getPrev()).append(suffix)));
            }
            // maybe there is a cycle that starts (and ends) in pos?
            final Collection<NonRootPosition> continuations = heapPos.getContinuations(pos);
            if (continuations != null) {
                for (final NonRootPosition continuation : continuations) {
                    todo.add(new Pair<>(pos.append(continuation), suffix));
                }
            }
        }
        return result;
    }

    /**
     * @param ref some reference
     * @param includeRef if true, the result also contains ref
     * @param eqGraph the equality graph
     * @param joiningStructures the joining structures
     * @return set of pairs, where each pair consists of a reference r that can
     * possibly be equal to ref (i.e. r =?= ref) or can reach ref (i.e. r -><-
     * ref). The second component of the pair is true iff we used a joins
     * annotation.
     */
    private static Collection<Pair<AbstractVariableReference, Boolean>> getSim(
        final AbstractVariableReference ref,
        final boolean includeRef,
        final EqualityGraph eqGraph,
        final JoiningStructures joiningStructures)
    {
        final Collection<Pair<AbstractVariableReference, Boolean>> result = new LinkedHashSet<>();
        if (includeRef) {
            result.add(new Pair<>(ref, Boolean.FALSE));
        }
        for (final AbstractVariableReference other : eqGraph.getPartners(ref)) {
            result.add(new Pair<>(other, Boolean.FALSE));
        }
        for (final AbstractVariableReference partner : joiningStructures.getReferencesWithPartner(ref)) {
            result.add(new Pair<>(partner, Boolean.TRUE));
        }
        return result;
    }

    /**
     * Add annotations needed to keep our state representation valid after
     * performing a PUTFIELD or AASTORE to an abstract instance or array, where
     * the new connection is not represented explicitly.
     * @param state State in which a write access connecting <code>parentRef
     *  </code> and <code>childRef</code> will occur <em>after</em> calling this
     * method.
     * @param parentRef abstract variable reference to the reference type value
     * written to.
     * @param newConnection the connection between <code>parentRef</code> and
     * <code>childRef</code> which is about to be created. May be null if the
     * exact connection isn't really known (ie for AbstractArrays)
     * @param childRef abstract variable reference to the value that is written.
     * @return information about changes in Defreach annotations that _must_ be regarded
     */
    public static Collection<DefiniteReachabilityAnnotationCreation> annotateAsNewAbstractChild(
        final State state,
        final AbstractVariableReference parentRef,
        final HeapEdge newConnection,
        final AbstractVariableReference childRef)
    {
        // first introduce annotations caused by the write
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach = AnnotationFixups
                .annotateAsNewConcreteChild(state, parentRef, newConnection, childRef, state, false);
        // then connect parent and child
        state.getHeapAnnotations().getJoiningStructures().add(parentRef, childRef);
        return newDefReach;
    }
}
