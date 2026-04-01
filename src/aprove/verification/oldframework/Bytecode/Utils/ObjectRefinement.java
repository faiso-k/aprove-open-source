package aprove.verification.oldframework.Bytecode.Utils;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.runtime.Options.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convenience class holding several routines needed in the refinement of
 * abstract instances.
 * @author Marc Brockschmidt
 */
public final class ObjectRefinement {

    /**
     * Private dummy constructor to prevent instantiation.
     */
    private ObjectRefinement() {
        assert (false) : "ObjectRefinement should never be instantiated";
    }

    /**
     * Performs an initialization refinement if needed.
     * @param parsedClass the class to initialize
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    public static boolean forInitialization(
        final IClass parsedClass,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        return forInitialization(parsedClass, curState, newStates, new LinkedList<>());
    }
    /**
     * Performs an initialization refinement if needed.
     * @param parsedClass the class to initialize
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    private static boolean forInitialization(
        final IClass parsedClass,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates,
        final Collection<Triple<ClassName, InitStatus, InitStatus>> initStates)
    {
        final ClassPath cPath = curState.getClassPath();
        JBCOptions options = curState.getJBCOptions();
        InitStatus defaultInitState = options.defaultClassInitState();
        final ClassName className = parsedClass.getClassName();
        final ClassInitializationInformation curInitInfo = curState.getClassInitInfo();
        final InitStatus wasInitialized = curInitInfo.getInitializationState(className, options);
        if (wasInitialized != InitStatus.MAYBE) {
            return false;
        }

        /*
         * For (uninitialied) classes with no code in the initializer and no
         * ConstantValue attribute we can just set the initialization state to
         * YES.
         */
        if (hasNoopInit(parsedClass, curInitInfo.getClassesWithInitializationState(options))) {
            final State newState = curState.clone();
            final ClassInitializationInformation newInitInfo = newState.getClassInitInfo();
            Collection<Triple<ClassName, InitStatus, InitStatus>> newInitStates = new LinkedList<>(initStates);

            IClass currentClass = parsedClass;
            while (currentClass != null) {
                newInitInfo.setInitialized(currentClass.getClassName(), InitStatus.YES);
                newInitStates.add(new Triple<>(currentClass.getClassName(), InitStatus.YES, InitStatus.MAYBE));
                final TypeTree superType = currentClass.getSuperType();
                if (superType == null) {
                    break;
                }
                currentClass = cPath.getClass(superType.getClassName());
                if (curInitInfo.getClassesWithInitializationState(options).get(superType.getClassName()) == InitStatus.RUNNING
                        || curInitInfo.getClassesWithInitializationState(options).get(superType.getClassName()) == InitStatus.YES)
                {
                    break;
                }
            }
            newStates.add(new Pair<State, EdgeInformation>(newState, new InitializationStateChange(newInitStates)));
            return true;
        }

        if (defaultInitState != InitStatus.NO) {
            final State newState = curState.clone();
            final ClassInitializationInformation newInitInfo = newState.getClassInitInfo();

            // produce case YES:
            Collection<Triple<ClassName, InitStatus, InitStatus>> newInitStates =
                    newInitInfo.setInitializedRecursively(newState, parsedClass);
            newInitStates.addAll(initStates);
            newStates.add(new Pair<State, EdgeInformation>(newState, new InitializationStateChange(newInitStates)));
        }

        if (defaultInitState != InitStatus.YES) {
            final State newState = curState.clone();
            final ClassInitializationInformation newInitInfo = newState.getClassInitInfo();
            Collection<Triple<ClassName, InitStatus, InitStatus>> newInitStates = new LinkedList<>(initStates);

            // produce case NO:
            newInitInfo.setInitialized(className, InitStatus.NO);
            newInitStates.add(new Triple<>(className, InitStatus.NO, InitStatus.MAYBE));

            /*
             * We decided that the current class is not initialized,  but did
             * not yet decide what the initialization state of the super classes
             * is. If there is no refinement needed for any super class, we can
             * just return the new state. To find this out, we call this method
             * recursively with the super class.
             */
            boolean superClassInitStateChanged = false;
            final Collection<Pair<State, ? extends EdgeInformation>> superClassNewStates = new LinkedHashSet<>();
            if (parsedClass.getSuperType() != null) {
                superClassInitStateChanged =
                    ObjectRefinement.forInitialization(
                        cPath.getClass(parsedClass.getSuperType().getClassName()),
                        newState,
                        superClassNewStates,
                        newInitStates);
            }

            if (superClassInitStateChanged) {
                /*
                 * The recursive call to forInitialization stored modified
                 * result states in "superClassNewStates". We need to take care
                 * that the evaluation history of these new states is reset.
                 */
                newStates.addAll(superClassNewStates);
            } else {
                newStates.add(new Pair<State, EdgeInformation>(newState, new InitializationStateChange(newInitStates)));
            }
        }
        return true;
    }

    /**
     * @param parsedClass the class
     * @param initStatus a map giving information about the initialization
     * status of the classes
     * @return true iff the init procedure of the class (also taking into
     * account the super types) does nothing at all.
     */
    public static boolean hasNoopInit(final IClass parsedClass, final Map<ClassName, InitStatus> initStatus) {
        if (!parsedClass.getStaticFields().isEmpty()) {
            return false;
        }
        for (final IMethod method : parsedClass.getMethods()) {
            if (method.isClassInitializer()) {
                return false;
            }
        }
        final TypeTree superTree = parsedClass.getSuperType();
        if (superTree != null) {
            final ClassName superName = superTree.getClassName();
            final InitStatus superInitStatus = initStatus.get(superName);
            if (superInitStatus != InitStatus.YES && superInitStatus != InitStatus.RUNNING) {
                // MAYBE or NO
                final IClass superClass = parsedClass.getClassPath().getClass(superName);
                if (!hasNoopInit(superClass, initStatus)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Performs an initialization refinement if needed.
     * @param important the class to initialize
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    public static boolean forInitialization(
        final Important important,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        final IClass parsedClass = curState.getClassPath().getClass(important.getClassName());
        return forInitialization(parsedClass, curState, newStates);
    }

    /**
     * Performs an existence refinement on the passed variable reference to an
     * abstract instance if needed.
     * @param refToRefine variable reference to refine
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    public static boolean forExistence(
        final AbstractVariableReference refToRefine,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        if (!curState.getHeapAnnotations().isMaybeExisting(refToRefine)) {
            return false;
        }

        final State newStateEx = curState.clone();

        //We had no information about this reference: create a fresh one
        final EdgeInformation infoEx;
        if (newStateEx.getAbstractVariable(refToRefine) == null) {
            final ObjectInstance oI = ConcreteInstance.newJLO(newStateEx);
            final AbstractVariableReference varRef = newStateEx.createReferenceAndAdd(oI, OperandType.ADDRESS);
            newStateEx.replaceReference(refToRefine, varRef);
            newStateEx.getHeapAnnotations().setExistenceIsKnown(varRef);
            infoEx = new RefinementEdge(refToRefine, varRef);
            //We had some structure information, just note that it exists:
        } else {
            assert (false) : "this should not happen";
            infoEx = null;
            newStateEx.getHeapAnnotations().setExistenceIsKnown(refToRefine);
        }

        final State newStateNonEx = curState.clone();
        final AbstractVariableReference nullRef = AbstractVariableReference.NULLREF;
        newStateNonEx.replaceReference(refToRefine, nullRef);
        newStateNonEx.getHeapAnnotations().setExistenceIsKnown(nullRef);
        final EdgeInformation infoNonEx = new RefinementEdge(refToRefine, nullRef);

        infoEx.add(new ExistenceCheck(refToRefine, true));
        infoNonEx.add(new ExistenceCheck(refToRefine, false));
        newStates.add(new Pair<>(newStateEx, infoEx));
        newStates.add(new Pair<>(newStateNonEx, infoNonEx));
        return true;
    }

    /**
     * Performs a type refinement on the passed variable reference to an
     * abstract instance if needed. The general idea here is that if we are
     * interested in some type T (which extends A) and have a reference to an
     * abstract instance O for which nothing but "is at least A" is known, we
     * need to generate a set of states in which O is either at least T or
     * definitely not T.
     * @param refToRefine variable reference to refine
     * @param typesOfInterest types to refine for
     * @param onlyInstantiable whether only instantiable classes should be
     * returned in this refinement.
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    public static boolean forTypesOfInterest(
        final AbstractVariableReference refToRefine,
        final List<FuzzyType> typesOfInterest,
        final boolean onlyInstantiable,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        // No refinement needed if this is the NULL pointer:
        if (refToRefine.isNULLRef()) {
            return false;
        }

        final AbstractType oldType = curState.getAbstractType(refToRefine);
        if (oldType.isConcrete()) {
            // nothing can be refined here
            return false;
        }

        final ClassPath cPath = curState.getClassPath();

        boolean changedSomething = false;
        // We only want to see non-abstract types in types of interest:
        if (Globals.useAssertions) {
            for (final FuzzyType f : typesOfInterest) {
                if (f instanceof FuzzyClassType) {
                    assert (f.isConcrete()) : "Trying to refine for abstract type " + f;
                }
            }

            final Set<FuzzyType> typesOfInterestSet = new LinkedHashSet<>(typesOfInterest);
            assert (typesOfInterestSet.size() == typesOfInterest.size()) : "Duplicates in typesOfInterest list "
                + typesOfInterest;
        }

        //Initialize result list for refinement:
        final ArrayList<Set<FuzzyType>> refinedTypes = new ArrayList<>(typesOfInterest.size() + 1);
        for (int i = 0; i < typesOfInterest.size() + 1; i++) {
            refinedTypes.add(new LinkedHashSet<FuzzyType>());
        }
        final Set<FuzzyType> valueTypes = oldType.expand(cPath, curState.getJBCOptions());

        for (final FuzzyType t : valueTypes) {
            ObjectRefinement.forTypesOfInterest(cPath, t, typesOfInterest, refinedTypes, curState);
        }

        final Collection<Pair<State, EdgeInformation>> tmpNewStates = new LinkedList<>();
        for (final Collection<FuzzyType> resultTypes : refinedTypes) {
            if (onlyInstantiable) {
                final Iterator<FuzzyType> typeIt = resultTypes.iterator();
                while (typeIt.hasNext()) {
                    final FuzzyType t = typeIt.next();
                    if (t instanceof FuzzyClassType && !t.isArrayType()) {
                        final TypeTree tt = cPath.getTypeTree((FuzzyClassType) t);
                        if (tt.isAbstract() || tt.isInterface()) {
                            typeIt.remove();
                        }
                    }
                }
            }
            if (resultTypes.isEmpty()) {
                continue;
            }

            final State newState = curState.clone();
            // Create a new reference used to replace the old one
            final AbstractVariable inst = newState.getAbstractVariable(refToRefine);
            final AbstractVariableReference newRef;
            if (inst != null) {
                newRef = newState.createReferenceAndAdd(inst, OperandType.ADDRESS);
            } else {
                newRef = AbstractVariableReference.create(refToRefine);
            }
            newState.replaceReference(refToRefine, newRef);
            final AbstractType newType = new AbstractType(cPath, curState.getJBCOptions(), resultTypes);
            if (!oldType.equals(newType)) {
                changedSomething = true;
            }
            newState.setAbstractType(newRef, newType);
            final RefinementEdge edge = new RefinementEdge(refToRefine, newRef);
            edge.add(new InstanceCast(refToRefine));
            tmpNewStates.add(new Pair<State, EdgeInformation>(newState, edge));
        }

        if (tmpNewStates.size() > 1 || changedSomething) {
            newStates.addAll(tmpNewStates);
            return true;
        }
        return false;
    }

    /**
     * @param cPath The considered class path for this analysis.
     * @param typeToRefine a type to refine
     * @param typesOfInterest a list of types for which we want to refine
     * @param result a list of collections of (sub)types of typeToRefine, each
     * list element result[i] chosen such that all its types match
     * typesOfInterest[i]. All non-matching types are collected in the last
     * element.
     */
    private static void forTypesOfInterest(
        final ClassPath cPath,
        final FuzzyType typeToRefine,
        final List<FuzzyType> typesOfInterest,
        final ArrayList<Set<FuzzyType>> result,
        State s)
    {

        if (Globals.useAssertions) {
            if (typeToRefine instanceof FuzzyClassType && !typeToRefine.isArrayType() && typeToRefine.isConcrete()) {
                final FuzzyClassType fct = (FuzzyClassType) typeToRefine;
                final ClassName minClass = fct.getMinimalClass();
                assert (!cPath.getTypeTree(minClass).isAbstract());
            }
        }

        int i = 0;
        int maximalArrayDimension = 0;

        //Check what (if any) of the types of interest are matched by typeToRefine
        final List<Integer> matchingTypes = new LinkedList<>();
        for (final FuzzyType typeOfInterest : typesOfInterest) {
            if (maximalArrayDimension < typeOfInterest.getArrayDimension()) {
                maximalArrayDimension = typeOfInterest.getArrayDimension();
            }

            if (typeToRefine.getArrayDimension() == typeOfInterest.getArrayDimension()) {
                if (typeToRefine instanceof FuzzyPrimitiveType
                    && typeOfInterest instanceof FuzzyPrimitiveType
                    && ((FuzzyPrimitiveType) typeToRefine).getPrimitiveType() == ((FuzzyPrimitiveType) typeOfInterest)
                        .getPrimitiveType())
                {
                    matchingTypes.add(i);
                } else if (typeToRefine instanceof FuzzyClassType && typeOfInterest instanceof FuzzyClassType) {
                    if (cPath.getTypeTree((FuzzyClassType) typeToRefine).instanceOf(
                        cPath.getTypeTree((FuzzyClassType) typeOfInterest)))
                    {
                        matchingTypes.add(i);
                    }
                }
                //If the array dimensions don't match, the only possible way of getting the
                //two types to match is to have a type to refine that is an array and is an
                //instance of the class type in the type of interest. Arrays extend
                //jlObject, implement Serializable and Cloneable:
            } else if (typeToRefine.getArrayDimension() > typeOfInterest.getArrayDimension()
                && typeOfInterest instanceof FuzzyClassType)
            {
                final FuzzyClassType typeOfInt = (FuzzyClassType) typeOfInterest;
                if (typeOfInt.isArrayParentClass()) {
                    matchingTypes.add(i);
                }
            }
            i++;
        }

        //typeToRefine matches more than one typeOfInterest. Choose the best.
        //This can only happen with FuzzyClass, as primitives match only one array:
        if (matchingTypes.size() > 1) {
            //Remove candidates:
            Outer: while (matchingTypes.size() > 1) {
                //Run through the set until you find m[0] instanceof m[j] or m[j] instanceof m[0],
                //then remove the upper one. Then jump back to the outer loop, until only one
                //type is left
                final TypeTree firstMatch =
                    cPath
                        .getClass(((FuzzyClassType) typesOfInterest.get(matchingTypes.get(0))).getMinimalClass())
                        .getType();
                for (final Integer j : matchingTypes) {
                    if (matchingTypes.get(0).equals(j)) {
                        continue;
                    }
                    final TypeTree curMatch =
                        cPath.getClass(((FuzzyClassType) typesOfInterest.get(j)).getMinimalClass()).getType();
                    if (firstMatch.instanceOf(curMatch)) {
                        matchingTypes.remove(j);
                        continue Outer;
                    } else if (curMatch.instanceOf(firstMatch)) {
                        matchingTypes.remove(0);
                        continue Outer;
                    }
                }
                throw new RuntimeException("Looks like there are orthogonal types ("
                    + matchingTypes
                    + " in "
                    + typesOfInterest
                    + ")"
                    + " matched by "
                    + typeToRefine);
            }
        }

        //Exactly one match. We win!
        if (matchingTypes.size() == 1) {
            result.get(matchingTypes.get(0)).add(typeToRefine);
        } else {
            //Check if this type is marked as maximal, otherwise recurse:
            if (typeToRefine instanceof FuzzyClassType && !typeToRefine.isConcrete()) {
                final FuzzyClassType typeToRef = (FuzzyClassType) typeToRefine;
                final TypeTree typeTreeToRefine = cPath.getClass(typeToRef.getMinimalClass()).getType();
                final LinkedHashSet<FuzzyType> subtypes = new LinkedHashSet<>();
                for (final TypeTree t : typeTreeToRefine.getSubTypes()) {
                    subtypes.add(new FuzzyClassType(t.getClassName(), false, typeToRefine.getArrayDimension()));
                }
                for (final TypeTree t : typeTreeToRefine.getImplementingTypes()) {
                    subtypes.add(new FuzzyClassType(t.getClassName(), false, typeToRefine.getArrayDimension()));
                }
                //Array types are special: They are all instances of Object and
                //implement the Serializable and Cloneable interfaces. Unfold them
                //until we are sure that they are not important:
                if (typeToRef.getArrayDimension() <= maximalArrayDimension) {
                    typeToRef.expandToArrays(subtypes);
                } else {
                    typeToRef.expandToArrays(result.get(typesOfInterest.size()));
                }

                for (final FuzzyType t : subtypes) {
                    ObjectRefinement.forTypesOfInterest(cPath, t, typesOfInterest, result, s);
                }

                //Push the current type into the non-matching set:
                result.get(typesOfInterest.size()).add(
                    new FuzzyClassType(typeToRef.getMinimalClass(), true, typeToRef.getArrayDimension()));
            } else {
                result.get(typesOfInterest.size()).add(typeToRefine);
            }
        }
    }

    /**
     * Performs a type refinement on the passed variable reference to an
     * abstract instance if needed. The general idea here is that if we are
     * interested in some type T (which extends A) and have a reference to an
     * abstract instance O for which nothing but "is at least A" is known, we
     * need to generate a set of states in which O is either at least T or
     * definitely not T.
     * @param refToRefine variable reference to refine
     * @param typeOfInterest type to refine for
     * @param onlyInstantiable whether only instantiable classes should be
     * returned in this refinement.
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    public static boolean forTypeOfInterest(
        final AbstractVariableReference refToRefine,
        final FuzzyType typeOfInterest,
        final boolean onlyInstantiable,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        return forTypesOfInterest(
            refToRefine,
            Collections.singletonList(typeOfInterest),
            onlyInstantiable,
            curState,
            newStates);
    }

    /**
     * Performs, if needed, an equality refinement on the two variable
     * references.
     * @param refA variable reference to refine
     * @param refB variable reference to refine
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @param needStates if false, we do not compute states for newStates, but
     * just return true/false
     * @return true iff existence refinement was needed
     */
    public static boolean forEquality(
        final AbstractVariableReference refA,
        final AbstractVariableReference refB,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates,
        final boolean needStates)
    {

        // TODO When writing b.f=c with a.f=b, should we also refine a=?=z? Currently we just refine b=?=y.

        if (refA.equals(refB)) {
            return false;
        }

        // the annotation is not transitive, so we do not need to consider long paths!
        if (!curState.getHeapAnnotations().getEqualityGraph().areMarkedAsPossiblyEqual(refA, refB)) {
            return false;
        }

        // we must not remove =?= for NRIRs
        final Collection<AbstractVariableReference> nrirs = curState.getAllNRIRs();
        if (nrirs.contains(refA) || nrirs.contains(refB)) {
            return false;
        }
        if (!needStates) {
            return true;
        }

        // Do the non-equality first:
        final State newNonEQState = curState.clone();

        newNonEQState.getHeapAnnotations().getEqualityGraph().remove(refA, refB);
        newStates.add(new Pair<State, EdgeInformation>(newNonEQState, new NEQRefinementEdge(refA, refB)));

        // now on to the equality
        final State newEQState = curState.clone();

        /*
         * Always replace with the more realized instance (otherwise replaceReferenceInDefiniteReachabilityAnnotations
         * fails). TODO: Is this really needed? Throw out replace...DefReach... and let the intersector work?
         */
        final Pair<AbstractVariableReference, AbstractVariableReference> pair =
            determineDirectionOfReplacement(curState, refA, refB);
        final AbstractVariableReference replacedRef = pair.x;
        final AbstractVariableReference replacementRef = pair.y;

        newEQState.replaceReferencesWithoutAnnotations(replacedRef, replacementRef);

        final Collection<DefiniteReachabilityAnnotationCreation> newInfo =
            newEQState
                .getHeapAnnotations()
                .getDefiniteReachabilities()
                .replaceReference(newEQState, replacedRef, replacementRef);

        newEQState.getHeapAnnotations().getEqualityGraph().remove(refA, refB);

        newEQState.gc();

        /*
         * Intersect the original state with the one where we replaced. If the two references can be equal, the result
         * is a state with very precise information.
         */
        Triple<State, Map<AbstractVariableReference, AbstractVariableReference>, Map<AbstractVariableReference, AbstractVariableReference>> intersectorResult;
        try {
            intersectorResult = Intersector.intersectAndRename(newEQState, curState);
        } catch (final IntersectionFailException e) {
            newStates.add(new Pair<State, EdgeInformation>(newEQState, new FailedRefinementEdge(replacedRef
                + "/"
                + replacementRef
                + ": "
                + e)));
            return true;
        }
        final State intersected = intersectorResult.x;

        /*
         * Try to find out if we found out that some reference is now a
         * "cycle joint", meaning that this is the point where a cycle
         * "starts" (i.e. it has some reference to the outside world).
         *
         * In the algorithm we are interested in (in-place reversal), we reach
         * this joint twice:
         *  (1) We run down the "handle" of a pan-handle list and reach the
         *      joint for the first time. We want to keep the information that
         *      we will reach this joint again, but remove the rest of the
         *      info.
         *  (2) We have run through the "pan" of a pan-handle list and reach the
         *      joint for a second time. We now want to leave the cycle. The
         *      annotation is now wrong.
         * In phase (2), we are save because the rest of the list is acyclic.
         * For the first part, however, we need some magic to create this shape,
         * and use pseudo-field "...!cycleJoint" to give the first reference
         * on the cycle a name. We connect everything with def. reaches and
         * then need to clean up a bit once we reach this pseudo-field entry.
         * That's what's happening here:
         */
        boolean doNotMergeLoop = false;
        final AbstractVariableReference intersectorReplacementRef = intersectorResult.y.get(replacementRef);
        final AbstractVariable replacementValue = intersected.getAbstractVariable(intersectorReplacementRef);
        if (replacementValue instanceof ConcreteInstance) {
            final ConcreteInstance replacementInstance =
                (ConcreteInstance) intersected.getAbstractVariable(intersectorReplacementRef);
            final TypeTree objectClass =
                intersected.getClassPath().getTypeTree(ClassName.Important.JAVA_LANG_OBJECT.getClassName());
            final ConcreteInstance jLOSliceOfreplacementInstance =
                replacementInstance.getConcreteInstanceSliceAtType(objectClass);
            for (final Map.Entry<String, AbstractVariableReference> entry : jLOSliceOfreplacementInstance
                .getFields()
                .entrySet())
            {
                if (entry.getKey().endsWith("!cycleJoint")) {
                    jLOSliceOfreplacementInstance.removeField(entry.getKey());
                    doNotMergeLoop = true;
                    break;
                }
            }
        }

        final EQRefinementEdge edge = new EQRefinementEdge(refA + " = " + intersectorReplacementRef, intersectorReplacementRef, refA, doNotMergeLoop);
        edge.addAll(newInfo);
        newStates.add(new Pair<State, EdgeInformation>(intersected, edge));
        return true;
    }

    /**
     * Find out which of the two references should be replaced and which should
     * be used as the replacement.
     * @param curState the state before the refinement
     * @param leftRef =?= rightRef
     * @param rightRef =?= leftRef
     * @return a pair with the replaced reference as the first component and the
     * replacement reference as the second component.
     */
    private static Pair<AbstractVariableReference, AbstractVariableReference> determineDirectionOfReplacement(
        final State curState,
        final AbstractVariableReference leftRef,
        final AbstractVariableReference rightRef)
    {
        final AbstractVariable leftVar = curState.getAbstractVariable(leftRef);
        final AbstractVariable rightVar = curState.getAbstractVariable(rightRef);
        final AbstractVariableReference replacedRef;
        final AbstractVariableReference replacementRef;

        if (rightVar == null && leftVar != null) {
            replacedRef = rightRef;
            replacementRef = leftRef;
        } else if (rightVar != null && leftVar == null) {
            replacedRef = leftRef;
            replacementRef = rightRef;
        } else {
            /*
             * If both instances are known to exist, it should be the case that
             * at least one of them is realized just up to java.lang.Object
             * (without any field).
             */
            if (leftVar instanceof Array || rightVar instanceof AbstractInstance) {
                replacedRef = rightRef;
                replacementRef = leftRef;
            } else if (rightVar instanceof Array || leftVar instanceof AbstractInstance) {
                replacedRef = leftRef;
                replacementRef = rightRef;
            } else {
                // both are ConcreteInstances
                final ConcreteInstance aiLeft = (ConcreteInstance) leftVar;
                if (aiLeft != null && aiLeft.isOnlyRealizedUpToJLO()) {
                    replacedRef = leftRef;
                    replacementRef = rightRef;
                } else {
                    replacedRef = rightRef;
                    replacementRef = leftRef;
                }
            }
        }
        return new Pair<>(replacedRef, replacementRef);
    }

    /**
     * Take care that the state contains an explicit representation for the
     * given reference up to the given type. All annotations are regarded.
     * @param objectRef a reference
     * @param typeToRealize the type to realize
     * @param fieldName name of the field we want to access (null: realize all fields)
     * @param curState the base state
     * @param newStates new states (with refine edges) will be added here
     * @param needStates if false, we do not compute states for newStates, but
     * just return true/false
     * @return true if refinement was needed
     */
    public static boolean forRealization(
        final AbstractVariableReference objectRef,
        final TypeTree typeToRealize,
        final String fieldName,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates,
        final boolean needStates)
    {

        /*
         * The code dealing with panhandle lists (having a cycle joint) more or less assumes no =?= annotation exists
         * for realized instances in the panhandle structure. If we have a cycle joint in objectRef, we want to enforce
         * refinement.
         */
        final AbstractVariable var = curState.getAbstractVariable(objectRef);
        boolean cycleJoint = false;
        if (var != null && var instanceof ConcreteInstance) {
            final ConcreteInstance oI = (ConcreteInstance) var;
            for (final Entry<FieldIdentifier, AbstractVariableReference> entry : oI.getAllFields().entrySet()) {
                if (entry.getKey().getFieldName().endsWith("!cycleJoint")) {
                    cycleJoint = true;
                    break;
                }
            }
        }

        final Collection<AbstractVariableReference> refineEQ = new LinkedHashSet<>();
        if (cycleJoint) {
            refineEQ.addAll(curState.getHeapAnnotations().getEqualityGraph().getPartners(objectRef));
            refineEQ.removeAll(curState.getAllNRIRs());
        }

        /*
         * We also need to refine objectRef =?= x if there is some annotation x -!!-> objectRef. Consider a cycle
         * starting in objectRef. If we run through the cycle using a variable x and now are at the top again, the
         * information x -!!-> objectRef still holds, but this represents another cycle run. In the TRS we need to
         * re-set the "length" of the DefReach annotation to another cycle run so that we do not prove termination here.
         */
        for (final DefiniteReachabilityAnnotation defReach : curState.getHeapAnnotations().getDefiniteReachabilities())
        {
            if (defReach.getTo().equals(objectRef)) {
                if (curState
                    .getHeapAnnotations()
                    .getEqualityGraph()
                    .areMarkedAsPossiblyEqual(defReach.getFrom(), objectRef))
                {
                    refineEQ.add(defReach.getFrom());
                }
            }
        }

        for (final AbstractVariableReference partnerRef : refineEQ) {
            final boolean doneSomething = forEquality(objectRef, partnerRef, curState, newStates, needStates);

            if (doneSomething) {
                // yes, only do a single refinement here
                return true;
            }
        }
        final AbstractVariable av = curState.getAbstractVariable(objectRef);

        //No realization refinement for abstract instances:
        if (av instanceof AbstractInstance) {
            return false;
        }

        assert (av instanceof ConcreteInstance);
        if (av.isNULL()) {
            return false;
        }
        final ConcreteInstance inst = (ConcreteInstance) av;
        if (inst.getMostSpecializedInstance().getType().isSubClassOf(typeToRealize)) {
            // find the slice of the type we are interested in and make sure that all fields are realized
            ConcreteInstance current = inst.getMostSpecializedInstance();
            while (current != null) {
                if (current.getType().equals(typeToRealize)) {
                    break;
                }
                current = current.getSuperClassInstance();
            }
            assert (current != null);
            assert (current.getType().equals(typeToRealize));
            if (!current.hasUnrealizedField()) {
                // all fields are there, no need to refine
                return false;
            } else if (fieldName != null) {
                // Maybe we just want to access some field? Then it might be okay to have _other_ unrealized fields.
                if (current.getFields().get(fieldName) != null) {
                    return false;
                }
            }
        }

        final ClassPath cPath = curState.getClassPath();
        final IClass parsedClass = cPath.getClass(typeToRealize.getClassName());
        if (forInitialization(parsedClass, curState, newStates)) {
            return true;
        }

        final FuzzyClassType classToRealize = new FuzzyClassType(typeToRealize.getClassName(), true);

        if (forTypeOfInterest(objectRef, classToRealize, true, curState, newStates)) {
            return true;
        }

        final State clone = curState.clone();

        /*
         * Check if the type we want to realize to is actually a subtype of
         * the instance type recorded in the state.
         */
        final AbstractType instType = curState.getAbstractType(objectRef);
        for (final FuzzyType possibleClass : instType.getPossibleClassesCopy()) {
            assert (!(possibleClass instanceof FuzzyPrimitiveType));
            final FuzzyClassType fct = (FuzzyClassType) possibleClass;
            final ClassName minClass = fct.getMinimalClass();
            final TypeTree typeTree = cPath.getTypeTree(minClass);
            if (!typeTree.isSubClassOf(typeToRealize)) {
                assert (false);
            }
        }

        final AbstractVariableReference realizedRef = AbstractVariableReference.create(inst, OperandType.ADDRESS);
        final ConcreteInstance instanceToRealize = (ConcreteInstance) clone.getAbstractVariable(objectRef);
        clone.replaceReference(objectRef, realizedRef);
        clone.addAbstractVariable(realizedRef, instanceToRealize);

        // fill the instance with more slices and references in the fields
        final Collection<Pair<HeapEdge, AbstractVariableReference>> childInstanceRefs =
            instanceToRealize.realizeUpTo(clone, realizedRef, typeToRealize);
        final RefinementEdge edge = new RealizationRefinementEdge(objectRef, realizedRef);
        if (!childInstanceRefs.isEmpty()) {
            final Collection<VariableInformation> newInfo =
                VariableInitialization.annotateAsFreshChildRefs(
                    clone,
                    realizedRef,
                    childInstanceRefs,
                    curState,
                    objectRef);
            edge.addAll(newInfo);

            final IClass objectClass = clone.getClassPath().getClass(JAVA_LANG_OBJECT);
            for (final Pair<HeapEdge, AbstractVariableReference> pair : childInstanceRefs) {
                final InstanceFieldEdge fieldEdge = ((InstanceFieldEdge) pair.x);
                final AbstractVariableReference cycleJointField =
                    instanceToRealize.getField(
                        objectClass.getClassName(),
                        fieldEdge.getFieldName() + "!cycleJoint",
                        true);
                if (cycleJointField != null) {
                    final ConcreteInstance childInstance = (ConcreteInstance) clone.getAbstractVariable(pair.y);
                    if (childInstance != null) {
                        childInstance.getConcreteInstanceSliceAtType(objectClass.getClassName()).setField(
                            fieldEdge.getFieldName() + "!cycleJoint",
                            cycleJointField);
                    }
                }
            }
        }


        /*
         * Strings: We know that count and offset are positive integers, so
         * mark them as such.
         */
        final FuzzyType fTypeToRealize = new FuzzyClassType(typeToRealize.getClassName(), true);
        if (fTypeToRealize.equals(FuzzyClassType.FT_JAVA_LANG_STRING)) {
            final Collection<DefiniteReachabilityAnnotationCreation> newDefReach = new LinkedHashSet<>();
            final ClassName jlStringClassName = ClassName.Important.JAVA_LANG_STRING.getClassName();
            final AbstractInt nonNegInt =
                    AbstractInt.create(
                            IntervalBound.ZERO,
                            IntegerType.UNBOUND.getUpper(),
                            IntervalBound.ZERO,
                            IntegerType.UNBOUND.getUpper(),
                            0,
                            0);

            if (instanceToRealize.getField(jlStringClassName, "count", true) != null) {
                final AbstractVariableReference nonNegativeCountRef =
                        clone.createReferenceAndAdd(nonNegInt, OperandType.INTEGER);
                newDefReach.addAll(instanceToRealize.putField(clone, null, jlStringClassName, "count", nonNegativeCountRef));
                edge.add(new JBCIntegerRelation(nonNegativeCountRef, IntegerRelationType.GE, 0));
            }

            if (instanceToRealize.getField(jlStringClassName, "offset", true) != null) {
                final AbstractVariableReference nonNegativeOffsetRef =
                        clone.createReferenceAndAdd(nonNegInt, OperandType.INTEGER);
                newDefReach.addAll(instanceToRealize.putField(clone, null, jlStringClassName, "offset", nonNegativeOffsetRef));
                edge.add(new JBCIntegerRelation(nonNegativeOffsetRef, IntegerRelationType.GE, 0));
            }

            edge.addAll(newDefReach);
        }

        newStates.add(new Pair<State, EdgeInformation>(clone, edge));
        return true;
    }

    /**
     * Make sure that there is no ref =?= x for any x that may have fields.
     * @param ref a reference
     * @param state a state
     * @param result the resulting states
     * @return true iff we did some refinement
     */
    public static boolean forEquality(
        final AbstractVariableReference ref,
        final State state,
        final Collection<Pair<State, ? extends EdgeInformation>> result)
    {
        for (final AbstractVariableReference partner : state.getHeapAnnotations().getEqualityGraph().getPartners(ref)) {
            if (!state.canHaveFields(partner)) {
                continue;
            }
            if (forEquality(ref, partner, state, result, true)) {
                return true;
            }
        }
        return false;
    }
}
