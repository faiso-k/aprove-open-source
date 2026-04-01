package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Representation of class and instance field accesses.
 * @author Marc Brockschmidt
 * @author Fabian K&uuml;rten
 */
public class FieldAccess extends OpCode {
    /**
     * Type of access, can be either static or instance.
     */
    public enum FieldAccessType {
        /**
         * Static access of class fields (not instance fields).
         */
        STATIC,

        /**
         * Access of instance fields.
         */
        INSTANCE
    }

    /**
     * Access is either writing or reading.
     */
    public enum FieldAccessRW {
        /**
         * Read a field.
         */
        READ,

        /**
         * Write a field.
         */
        WRITE
    }

    /**
     * Identifier of the field to access.
     */
    private final FieldIdentifier fieldId;

    /**
     * Type (static or instance) of access.
     */
    private final FieldAccessType accessType;

    /**
     * Direction of access (either read or write).
     */
    private final FieldAccessRW readWriteType;

    /**
     * @param fId Identifier of the field to access.
     * @param type Type (static or instance) of access.
     * @param rw Direction of access (either read or write).
     */
    public FieldAccess(final FieldIdentifier fId, final FieldAccessType type, final FieldAccessRW rw) {
        this.fieldId = fId;
        this.accessType = type;
        this.readWriteType = rw;
    }

    /**
     * @return String representation of this field access opcode
     */
    @Override
    public String toString() {
        String result;
        if (this.readWriteType == FieldAccessRW.READ) {
            result = "Read from ";
        } else {
            result = "Write to ";
        }
        result += this.fieldId.getFieldName();
        if (this.accessType == FieldAccess.FieldAccessType.STATIC) {
            result += " (static)";
        }
        return result;

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean needsRefine(final State s) {
        if (this.accessType != FieldAccessType.INSTANCE) {
            return super.needsRefine(s);
        }

        final Field field = this.resolveField(s);
        if (field == null) {
            return false;
        }
        final ClassPath cPath = s.getClassPath();
        final IClass fieldContainer = cPath.getClass(field.getClassName());

        return this.instanceRefine(
            s,
            new LinkedHashSet<Pair<State, ? extends EdgeInformation>>(),
            fieldContainer,
            false);
    }

    /**
     * @param s a state
     * @return the resolved field or null
     */
    private Field resolveField(final State s) {
        final ClassPath cPath = s.getClassPath();

        final IClass parsedClass = Resolver.resolveClass(cPath, this.fieldId.getClassName(), this);

        // If the class can't be resolved, we don't have to do anything, as the result of the
        // evaluation is determined to be a ClassDefNotFoundException
        if (parsedClass == null) {
            return null;
        }

        // If we can't resolve the field, we don't need to refine any further
        final Field field =
            Resolver
                .resolveField(parsedClass, this.fieldId.getFieldName(), this.getMethod().getIClass().getType());
        return field;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        final ClassPath cPath = s.getClassPath();

        final Field field = this.resolveField(s);
        if (field == null) {
            return false;
        }

        final IClass fieldContainer = cPath.getClass(field.getClassName());

        switch (this.accessType) {
        case STATIC:
            return this.staticRefine(s, out, fieldContainer);
        case INSTANCE:
            return this.instanceRefine(s, out, fieldContainer, true);
        default:
            assert (false) : "Unknown field access type";
            return false;
        }
    }

    /**
     * {@inheritDoc}}
     * @throws AbortionException if this method is aborted
     */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State s) throws AbortionException {
        final State newState = s.clone();
        final ClassPath cPath = s.getClassPath();
        final IClass parsedClass =
            Resolver.resolveClassOrThrow(cPath, this.fieldId.getClassName(), newState, this
                .getMethod()
                .getIClass()
                .getType());

        // If the class can't be loaded, we don't have to do anything, as the result of the
        // evaluation is determined to be a ClassDefNotFoundException
        if (parsedClass == null) {
            return new Pair<>(newState, new MethodStartEdge());
        }

        // If we can't resolve the field, we know what to do
        final Field field =
            Resolver.resolveFieldOrThrow(parsedClass, this.fieldId.getFieldName(), newState, this
                .getMethod()
                .getIClass()
                .getType());
        if (field == null) {
            return new Pair<>(newState, new MethodStartEdge());
        }
        final IClass fieldContainer = cPath.getClass(field.getClassName());

        switch (this.accessType) {
        case STATIC:
            return this.staticEval(s, newState, fieldContainer);
        case INSTANCE:
            return this.instanceEval(s, newState, fieldContainer);
        default:
            assert (false) : "Unknown field access type";
            return null;
        }
    }

    /**
     * @param curState current state
     * @param out list of states generated by refinements
     * @param fieldContainer Class actually containing the field
     * @return true if any refinement was needed
     */
    private boolean staticRefine(
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> out,
        final IClass fieldContainer)
    {
        final Field field = fieldContainer.getStaticFields().get(this.fieldId.getFieldName());
        if (field == null) {
            // IncompatibleClassChangeError
            return ObjectRefinement.forInitialization(INCOMPATIBLECLASSCHANGE_ERR, curState, out);
        }
        if (this.readWriteType == FieldAccessRW.WRITE && field.isFinal()) {
            final IMethod parsedMethod = this.getMethod();
            if (!fieldContainer.equals(parsedMethod.getIClass())) {
                // IllegalAccessError
                return ObjectRefinement.forInitialization(ILLEGALACCESS_ERR, curState, out);
            }
            if (!parsedMethod.isClassInitializer()) {
                // IllegalAccessError
                return ObjectRefinement.forInitialization(ILLEGALACCESS_ERR, curState, out);
            }
        }
        if (curState.getJBCOptions().defaultClassInitState() == InitStatus.YES) {
            AbstractVariableReference curValue = curState.getStaticFields().get(field.getClassName(), field.getName());
            if (curValue == null) {
                State newState = curState.clone();
                VariableInitialization.fillStaticFieldsWithGeneralValues(newState, fieldContainer);
                out.add(new Pair<>(newState, new RefinementEdge("filled static fields", Collections.emptyMap())));
                return true;
            }
        }
        // Try refining for initialization status
        return ObjectRefinement.forInitialization(fieldContainer, curState, out);
    }

    /**
     * Handles access to static fields.
     * @param curState state to work on
     * @param newState the state to modify for evaluation
     * @param fieldContainer The class actually containing the field
     * @return new state, either created by throwing an exception or by doing
     * the field access
     */
    private Pair<State, ? extends EdgeInformation> staticEval(
        final State curState,
        final State newState,
        final IClass fieldContainer)
    {
        // Check whether or not the field pointed at in the constant pool
        // actually names a static field
        final Field field = fieldContainer.getStaticFields().get(this.fieldId.getFieldName());
        if (field == null) {
            OpCode.throwException(newState, INCOMPATIBLECLASSCHANGE_ERR);
            return new Pair<>(newState, new MethodStartEdge());
        }

        final InitStatus initStatus = newState.getClassInitInfo().getInitializationState(fieldContainer.getClassName(), curState.getJBCOptions());
        final AbstractVariableReference accessedRef;
        if (!initStatus.equals(InitStatus.YES) && !initStatus.equals(InitStatus.RUNNING)) {
            assert (false) : "Tried to access static field of not definitely initialized class";
            accessedRef = null;
        } else {
            if (this.readWriteType == FieldAccessRW.READ) {
                if (Globals.DEBUG_COTTO) {
                    curState.getTerminationGraph().markStaticFieldAsInteresting(this.fieldId);
                }
                accessedRef =
                    curState.getStaticFields().get(fieldContainer.getClassName(), this.fieldId.getFieldName());
                newState.getCurrentStackFrame().pushOperandStack(accessedRef);
            } else {
                // Check if we are allowed to write the field (i.e. that it is not final)
                if (field.isFinal()) {
                    // The only exception here is: The field is declared in the current class,
                    // and the current method is its <clinit>
                    final IMethod method = this.getMethod();
                    if (!method.getIClass().equals(fieldContainer) || !method.isClassInitializer()) {
                        OpCode.throwException(newState, ILLEGALACCESS_ERR);
                        return new Pair<>(newState, new MethodStartEdge());
                    }
                }

                accessedRef = newState.getCurrentStackFrame().popOperandStack();
                final AbstractVariableReference oldContent =
                    newState.getStaticFields().get(fieldContainer.getClassName(), this.fieldId.getFieldName());
                newState.getStaticFields().set(fieldContainer.getClassName(), this.fieldId.getFieldName(), accessedRef);

                if (!oldContent.equals(accessedRef)) {
                    HeapPositions heapPos = new HeapPositions(newState);
                    for (final StackFrame sf : newState.getCallStack().getStackFrameList()) {
                        sf.getInputReferences().markStaticFieldAsChanged(heapPos, this.fieldId, accessedRef, oldContent);
                    }
                }
            }
            newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
        }

        // perform read/write
        final EvaluationEdge info = new EvaluationEdge();
        info.add(new StaticFieldAccessInformation(this.readWriteType, fieldContainer.getClassName(), this.fieldId
            .getFieldName(), accessedRef));

        return new Pair<>(newState, info);
    }

    /**
     * @param curState current state
     * @param out list of states generated by refinements
     * @param fieldContainer Class actually containing the field
     * @param needStates if false, we do not compute states for out, but just
     * return true/false
     * @return true if any refinement was needed
     */
    private boolean instanceRefine(
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> out,
        final IClass fieldContainer,
        final boolean needStates)
    {
        // If the field is static, no further refinement is needed
        final Field field = fieldContainer.getInstanceFields().get(this.fieldId.getFieldName());
        if (field == null) {
            return ObjectRefinement.forInitialization(Important.INCOMPATIBLECLASSCHANGE_ERR, curState, out);
        }

        if (this.readWriteType == FieldAccessRW.WRITE && field.isFinal()) {
            final IMethod parsedMethod = this.getMethod();
            if (!parsedMethod.isInstanceInitializer()) {
                // IllegalAccessError
                return ObjectRefinement.forInitialization(Important.ILLEGALACCESS_ERR, curState, out);
            }
        }

        // get the object ref to look at
        AbstractVariableReference objectRef;
        if (this.readWriteType == FieldAccessRW.WRITE) {
            objectRef = curState.getCurrentStackFrame().getOperandStack().peek(1);
        } else {
            objectRef = curState.getCurrentStackFrame().getOperandStack().peek(0);
        }

        // Find out if the instance exists
        if (ObjectRefinement.forExistence(objectRef, curState, out)) {
            return true;
        }

        if (objectRef.isNULLRef()) {
            return ObjectRefinement.forInitialization(Important.NPE_EXC, curState, out);
        }

        //This is a hack.
        final Collection<AbstractVariableReference> eqPartners =
            curState.getHeapAnnotations().getEqualityGraph().getPartners(objectRef);

        if (eqPartners.size() > 2) {
            final Collection<AbstractVariableReference> eqPartnersUsedOnlyOnHeap = new LinkedHashSet<>(eqPartners);

            //Remove references reachable from callstack:
            final Map<AbstractVariableReference, Integer> usedOnStackRefs = new DefaultValueMap<>(0);
            curState.getCallStack().getReferences(usedOnStackRefs);

            final Iterator<AbstractVariableReference> it = eqPartnersUsedOnlyOnHeap.iterator();
            while (it.hasNext()) {
                final AbstractVariableReference eqPartner = it.next();
                if (usedOnStackRefs.get(eqPartner) > 0) {
                    it.remove();
                }
            }

            if (this.readWriteType == FieldAccessRW.WRITE && eqPartnersUsedOnlyOnHeap.size() > 0) {
                /*
                 * Abstract away all references to objects containing only references
                 * unused on the stack, if they contain at least one of the eqPartners.
                 */
                final Map<AbstractVariableReference, Integer> usedInState = curState.getReferences();
                final Collection<AbstractVariableReference> refsToAbstract = new LinkedList<>();
                for (final Map.Entry<AbstractVariableReference, Integer> e : usedInState.entrySet()) {
                    final AbstractVariableReference ref = e.getKey();

                    //Skip the ref we want to access:
                    if (ref.equals(objectRef)) {
                        continue;
                    }

                    //Skip refs to primitives/arrays and used refs:
                    if (!ref.pointsToInstance() || usedOnStackRefs.get(ref) > 0) {
                        continue;
                    }

                    final AbstractVariable var = curState.getAbstractVariable(ref);
                    if (!(var instanceof ConcreteInstance)) {
                        continue;
                    }

                    final ConcreteInstance cI = (ConcreteInstance) var;
                    if (cI == ConcreteInstance.NULL || cI.isOnlyRealizedUpToJLO()) {
                        continue;
                    }

                    final Set<AbstractVariableReference> refsUsedInFields = cI.getFieldValues().keySet();
                    int eqPartnersUsedInFields = 0;
                    for (final AbstractVariableReference usedRef : refsUsedInFields) {
                        if (eqPartnersUsedOnlyOnHeap.contains(usedRef)) {
                            eqPartnersUsedInFields++;
                        }
                    }

                    if (eqPartnersUsedInFields >= 1) {
                        refsToAbstract.add(ref);
                    }
                }

                if (refsToAbstract.size() > 0) {
                    final State newState = curState.replaceConcreteInstancesByAbstractedInstance(refsToAbstract, false);
                    if (newState != null) {
                        out.add(new Pair<State, EdgeInformation>(newState, new InstanceEdge(
                            "Abstraction before field access.",
                            false)));
                        return true;
                    }
                }
            }
        }

        OUTER: if (this.readWriteType == FieldAccessRW.WRITE) {
            /*
             * In some write accesses, we want to guess some information about the state.
             * For that, we try to find a certain pattern, namely that we are currently
             * writing into a possibly cyclic list.
             * If the considered object o only has one reference field "n" and the reachable
             * types have only one as well and we know that the object might be cyclic in
             * that field, we refine into two cases:
             *  (1) The list is not cyclic.
             *  (2) The list is truly cyclic, i.e., the current ref can reach itself.
             *  (3) The list is a panhandle list, meaning that there is some reference
             *      j such that after some n-steps, o reaches j (i.e., o -[n]!-> j)
             *      and that j reaches itself (i.e., j -[n]!!-> j).
             * For (3), we add a pseudo-field "n!cycleJoint" to the object representation
             * of o, which contains a newly created j. We then add all the needed
             * annotations to j and try to continue;
             */
            final HeapAnnotations curAnnotations = curState.getHeapAnnotations();
            final CyclicStructures cyclicStructures = curAnnotations.getCyclicStructures();
            final AbstractVariable curObject = curState.getAbstractVariable(objectRef);
            if (curState.getJBCOptions().doCycleMagic
                && cyclicStructures.isCyclic(objectRef)
                && curObject instanceof ConcreteInstance)
            {
                final ImmutableSet<HeapEdge> cycleEdges = cyclicStructures.getNeededEdgesOf(objectRef);
                final ClassPath classPath = curState.getClassPath();

                if (cycleEdges.size() == 1) {
                    final ConcreteInstance concreteInstance = (ConcreteInstance) curObject;
                    if (!concreteInstance.getAllFields().containsKey(this.fieldId)) {
                        break OUTER;
                    }
                    final HeapEdge onlyEdge = cycleEdges.iterator().next();
                    AbstractType type = curState.getAbstractType(objectRef);
                    boolean haveOnlyRefFieldOnCycle;
                    if (type.getMinimalClass() == null) {
                        haveOnlyRefFieldOnCycle = false;
                    } else {
                        haveOnlyRefFieldOnCycle = classPath.reachableTypesHaveOnlyOneRefField(type.getMinimalClass().getMinimalClass(), curState.getJBCOptions());
                    }
                    final AbstractVariableReference nextObjectRef =
                        concreteInstance.getField(this.fieldId.getClassName(), this.fieldId.getFieldName());
                    if (haveOnlyRefFieldOnCycle
                        && onlyEdge instanceof InstanceFieldEdge
                        && ((InstanceFieldEdge) onlyEdge).getFieldName().equals(this.fieldId.getFieldName())
                        && curAnnotations.isMaybeExisting(nextObjectRef))
                    {

                        /*
                         * We only want to have parent=?=child (with parent.f=child), no other possible equality for
                         * parent.
                         */
                        for (final AbstractVariableReference partner : curAnnotations.getEqualityGraph().getPartners(
                            objectRef))
                        {
                            if (!partner.equals(nextObjectRef)) {
                                break OUTER;
                            }
                        }

                        final InstanceFieldEdge cycleEdge = ((InstanceFieldEdge) onlyEdge);

                        if (Globals.DEBUG_RICHARD) {
                            System.out.println("Cycle Determinisation");
                        }

                        ///////////////////////////////////////////////////////
                        //Prepare the acyclic case (find all reachable refs):
                        final State acyclicState = curState.clone();
                        final Set<AbstractVariableReference> seenRefs = new LinkedHashSet<>();
                        Reachability.followFields(objectRef, cycleEdges, seenRefs, objectRef, true, acyclicState);
                        seenRefs.add(objectRef);
                        for (final AbstractVariableReference ref : seenRefs) {
                            acyclicState.getHeapAnnotations().getCyclicStructures().remove(ref);
                            acyclicState.getHeapAnnotations().getPossiblyNonTreeRefs().remove(ref);
                        }
                        out.add(new Pair<>(acyclicState, new RefinementEdge(
                            "Cycle Determinisation (acyclic case)",
                            Collections.<AbstractVariableReference, AbstractVariableReference>emptyMap(),
                            true)));

                        ///////////////////////////////////////////////////////
                        //Prepare the cyclic case:
                        final State cyclicState = curState.clone();
                        seenRefs.clear();
                        final AbstractVariableReference lastRealizedRef =
                            Reachability.followFields(objectRef, cycleEdges, seenRefs, objectRef, true, cyclicState);
                        final HeapAnnotations cyclicStateAnnotations = cyclicState.getHeapAnnotations();
                        assert (!cyclicStateAnnotations.isMaybeExisting(objectRef));
                        cyclicStateAnnotations
                            .getDefiniteReachabilities()
                            .add(
                                new DefiniteReachabilityAnnotation(
                                    lastRealizedRef,
                                    objectRef,
                                    cycleEdges,
                                    false,
                                    classPath));
                        for (final AbstractVariableReference ref : seenRefs) {
                            //If we are in the cyclic case, our successor definitely exists (otherwise, the cycle would be broken!)
                            if (cyclicStateAnnotations.isMaybeExisting(ref)) {
                                if (cyclicState.getAbstractVariable(ref) == null) {
                                    cyclicState
                                        .addAbstractVariable(nextObjectRef, ConcreteInstance.newJLO(cyclicState));
                                }
                                cyclicStateAnnotations.setExistenceIsKnown(ref);
                            }
                        }
                        out.add(new Pair<>(cyclicState, new RefinementEdge(
                            "Cycle Determinisation (cyclic case)",
                            Collections.<AbstractVariableReference, AbstractVariableReference>emptyMap(),
                            true)));

                        ///////////////////////////////////////////////////////
                        //Prepare the state for the panhandle case:
                        final State panhandleState = curState.clone();
                        final HeapAnnotations panhandleStateAnnotations = panhandleState.getHeapAnnotations();

                        //Create (unrealized) instance and reference for the joint:
                        final IClass jointClass = classPath.getClass(cycleEdge.getClassName());
                        final ConcreteInstance jointInstance = ConcreteInstance.newJLO(panhandleState);
                        final AbstractVariableReference jointRef =
                            AbstractVariableReference.create(jointInstance, OperandType.ADDRESS);
                        panhandleState.addAbstractVariable(jointRef, jointInstance);
                        panhandleState.getHeapAnnotations().setAbstractType(
                            jointRef,
                            new AbstractType(classPath, new FuzzyClassType(jointClass.getClassName(), true)));
                        panhandleState.getHeapAnnotations().setReachableTypes(
                            jointRef,
                            curState.getHeapAnnotations().getAbstractType(objectRef));

                        //If we are in the panhandle case, our successor definitely exists (otherwise, the pan's handle would be broken!)
                        if (panhandleStateAnnotations.isMaybeExisting(nextObjectRef)) {
                            if (panhandleState.getAbstractVariable(nextObjectRef) == null) {
                                panhandleState.addAbstractVariable(
                                    nextObjectRef,
                                    ConcreteInstance.newJLO(panhandleState));
                            }
                            panhandleStateAnnotations.setExistenceIsKnown(nextObjectRef);
                        }

                        /*
                         * In the panhandle case, we know that the cycle will happen in the future, so we don't need
                         * no joins between parent and child!
                         */
                        panhandleStateAnnotations.getJoiningStructures().remove(objectRef, nextObjectRef);

                        //Add the joint to the next object:
                        final ConcreteInstance nextObjectInstance =
                            (ConcreteInstance) panhandleState.getAbstractVariable(nextObjectRef);
                        nextObjectInstance.setField(cycleEdge.getFieldName() + "!cycleJoint", jointRef);

                        //Copy joining references over:
                        for (final AbstractVariableReference ref : panhandleStateAnnotations
                            .getJoiningStructures()
                            .getReferencesWithPartner(objectRef))
                        {
                            panhandleStateAnnotations.getJoiningStructures().add(ref, objectRef);
                        }

                        //Add the new connections:
                        panhandleStateAnnotations.getEqualityGraph().addPossibleEquality(
                            panhandleState,
                            nextObjectRef,
                            jointRef);
                        panhandleStateAnnotations.getJoiningStructures().add(nextObjectRef, jointRef);
                        panhandleState
                            .getHeapAnnotations()
                            .getDefiniteReachabilities()
                            .add(
                                new DefiniteReachabilityAnnotation(
                                    nextObjectRef,
                                    jointRef,
                                    cycleEdges,
                                    false,
                                    classPath));

                        panhandleStateAnnotations.getJoiningStructures().add(jointRef, jointRef);
                        panhandleStateAnnotations.getDefiniteReachabilities().add(
                            new DefiniteReachabilityAnnotation(jointRef, jointRef, cycleEdges, true, classPath));

                        //Make the joint cyclic, too:
                        panhandleStateAnnotations.getCyclicStructures().add(jointRef, cycleEdges);
                        panhandleStateAnnotations.getPossiblyNonTreeRefs().add(jointRef);

                        out.add(new Pair<>(panhandleState, new RefinementEdge(
                            "Cycle Determinisation (panhandle case)",
                            Collections.<AbstractVariableReference, AbstractVariableReference>emptyMap(),
                            true)));
                        return true;
                    }
                }
            }
        }

        /*
         * Realize the state so that it has explicit information for the field. Here, all annotations are regarded when
         * creating the explicit instance representation.
         */
        if (ObjectRefinement.forRealization(
            objectRef,
            fieldContainer.getType(),
            field.getName(),
            curState,
            out,
            needStates))
        {
            return true;
        }

        if (this.readWriteType == FieldAccessRW.WRITE && ObjectRefinement.forEquality(objectRef, curState, out)) {
            return true;
        }

        return false;
    }

    /**
     * Handles access to instance fields.
     * @param curState state to work on
     * @param newState the state to modify for evaluation
     * @param fieldContainer The class actually containing the field
     * @return new state, either created by throwing an exception or by doing
     * the field access
     * @throws AbortionException if this method is aborted
     */
    private Pair<State, ? extends EdgeInformation> instanceEval(
        final State curState,
        final State newState,
        final IClass fieldContainer) throws AbortionException
    {
        // If the field is static, we just have to throw an exception
        final Field field = fieldContainer.getInstanceFields().get(this.fieldId.getFieldName());
        if (field == null) {
            OpCode.throwException(newState, INCOMPATIBLECLASSCHANGE_ERR);
            return new Pair<>(newState, new MethodStartEdge());
        }

        // Get the reference to access
        final AbstractVariableReference objectRef;
        if (this.readWriteType == FieldAccess.FieldAccessRW.WRITE) {
            objectRef = curState.getCurrentStackFrame().getOperandStack().peek(1);
        } else {
            objectRef = curState.getCurrentStackFrame().getOperandStack().peek(0);
        }

        if (this.readWriteType == FieldAccess.FieldAccessRW.WRITE) {
            // Check if we are allowed to write the field (i.e. that it is not final)
            if (field.isFinal()) {
                // The only exception here is: The field is declared in the current class,
                // and the current method is one of its <init>s
                final IMethod method = this.getMethod();
                if (!method.getIClass().equals(fieldContainer) || !method.isInstanceInitializer()) {
                    OpCode.throwException(newState, ILLEGALACCESS_ERR);
                    return new Pair<>(newState, new MethodStartEdge());
                }
            }
        }

        // Get the matching object
        final ObjectInstance object = (ObjectInstance) newState.getAbstractVariable(objectRef);

        // Check for nullness
        if (object.isNULL()) {
            OpCode.throwException(newState, NPE_EXC);
            return new Pair<>(newState, new MethodStartEdge());
        }

        final InitStatus initStatus = newState.getClassInitInfo().getInitializationState(fieldContainer.getClassName(), curState.getJBCOptions());
        if (!initStatus.equals(InitStatus.YES) && !initStatus.equals(InitStatus.RUNNING)) {
            assert (false) : "Tried to access field of not definitely initialized class";
        }

        // perform read/write
        final EvaluationEdge info = new EvaluationEdge();
        if (this.readWriteType == FieldAccessRW.WRITE) {

            final AbstractVariableReference value = curState.getCurrentStackFrame().getOperandStack().peek(0);

            AbstractVariableReference overwrittenRef = null;
            if (object instanceof AbstractInstance) {
                info.add(new AbstractInstanceAccessInformation(FieldAccessRW.WRITE, objectRef, value, fieldContainer
                    .getClassName(), this.fieldId.getFieldName()));
            } else {
                overwrittenRef =
                    object.getField(newState, objectRef, fieldContainer.getClassName(), this.fieldId.getFieldName());
                info.add(new InstanceAccessInformation(
                    FieldAccessRW.WRITE,
                    objectRef,
                    overwrittenRef,
                    value,
                    fieldContainer.getClassName(),
                    this.fieldId.getFieldName()));
            }

            /*
             * remove annotations that are definitely destroyed by the write access.
             * For that, find out if
             *  (1) The written reference r is annotated with @{f}
             *  (2) All references reachable from r have only one reference field.
             *  (3) The written reference r (in the old state) definitely reaches r
             *      (either by existing connection or annotation)
             * If that is the case, writing a new reference into the only field of r
             * breaks the existing cycle.
             *
             * Hence, we can now already remove the non-tree cyclic annotations on
             * r and all the reached successors. If the write might add another cycle
             * AnnotationFixups will take care of that.
             */

            final HeapAnnotations newStateAnnotations = newState.getHeapAnnotations();

            //Condition (1)
            ImmutableSet<HeapEdge> cycleEdges = null;
            HeapEdge singleCycleEdge = null;
            final CyclicStructures newCyclicStructures = newStateAnnotations.getCyclicStructures();
            if (newCyclicStructures.isCyclic(objectRef)) {
                cycleEdges = newCyclicStructures.getNeededEdgesOf(objectRef);
                if (cycleEdges != null && cycleEdges.size() == 1) {
                    singleCycleEdge = cycleEdges.iterator().next();
                    if (!(singleCycleEdge instanceof InstanceFieldEdge)) {
                        singleCycleEdge = null;
                    }
                }
            }

            //Condition (2)
            final AbstractType aT = curState.getAbstractType(objectRef);
            final boolean haveOnlyRefFieldOnCycle;
            if (aT.isConcrete()) {
                final ClassName minClass = aT.getMinimalClass().getMinimalClass();
                final ClassPath classPath = curState.getClassPath();
                haveOnlyRefFieldOnCycle = classPath.reachableTypesHaveOnlyOneRefField(minClass, curState.getJBCOptions());
            } else {
                haveOnlyRefFieldOnCycle = false;
            }

            //Condition (3)
            boolean oldAbstractCycleDestroyed = false;
            final Collection<AbstractVariableReference> refsOnCycle = new LinkedHashSet<>();

            //Check if the edge on the cycle is the written edge (and not a primitive or something):
            if (singleCycleEdge != null
                && haveOnlyRefFieldOnCycle
                && ((InstanceFieldEdge) singleCycleEdge).getFieldName().equals(this.fieldId.getFieldName()))
            {
                final AbstractVariableReference nextRef =
                    Reachability.followFields(objectRef, cycleEdges, refsOnCycle, objectRef, true, newState);
                //Reached directly:
                if (objectRef.equals(nextRef)) {
                    oldAbstractCycleDestroyed = true;
                } else if (nextRef != null) {
                    //Reached by annotation:
                    if (newStateAnnotations.getDefiniteReachabilities().areConnected(nextRef, objectRef, cycleEdges)) {
                        oldAbstractCycleDestroyed = true;
                    }
                }
            }

            //Check if the new content will just create a new cycle:
            boolean newAbstractCycleCreated = false;
            final Set<AbstractVariableReference> trash = new LinkedHashSet<>();
            final Set<HeapEdge> writtenHeapEdge =
                Collections.singleton((HeapEdge) new InstanceFieldEdge(fieldContainer.getClassName(), this.fieldId
                    .getFieldName()));
            final AbstractVariableReference valueEndRef =
                Reachability.followFields(value, writtenHeapEdge, trash, objectRef, false, newState);
            if (objectRef == valueEndRef
                || curState.getHeapAnnotations().getJoiningStructures().areJoining(valueEndRef, objectRef))
            {
                newAbstractCycleCreated = true;
            }

            if (oldAbstractCycleDestroyed && !newAbstractCycleCreated) {
                newCyclicStructures.remove(objectRef);
                newStateAnnotations.getPossiblyNonTreeRefs().remove(objectRef);

                for (final AbstractVariableReference refOnCycle : refsOnCycle) {
                    newStateAnnotations.getCyclicStructures().remove(refOnCycle);
                    newStateAnnotations.getPossiblyNonTreeRefs().remove(refOnCycle);
                    newStateAnnotations.getJoiningStructures().remove(refOnCycle, refOnCycle);
                }
            }

            // this method also takes care of all the annotation voodoo
            final Collection<DefiniteReachabilityAnnotationCreation> newDefReach =
                object.putField(newState, objectRef, fieldContainer.getClassName(), this.fieldId.getFieldName(), value);
            info.addAll(newDefReach);

            trash.clear();

            if (oldAbstractCycleDestroyed) {
                // This annotation is falsely removed by AnnotationFixups.removeAnnotationsIntroducingForbiddenShapes,
                // because it takes our changed newState as a basis for its calculations.
                newState.getHeapAnnotations().getJoiningStructures().add(overwrittenRef, objectRef);
            }

            // Remove the references after taking care of annotations
            newState.getCurrentStackFrame().popOperandStack();
            newState.getCurrentStackFrame().popOperandStack();
        } else {
            final AbstractVariableReference resultRef =
                object.getField(newState, objectRef, fieldContainer.getClassName(), this.fieldId.getFieldName());
            if (object instanceof AbstractInstance) {
                info.add(new AbstractInstanceAccessInformation(FieldAccessRW.READ, objectRef, resultRef, fieldContainer
                    .getClassName(), this.fieldId.getFieldName()));
            } else {
                info.add(new InstanceAccessInformation(FieldAccessRW.READ, objectRef, null, resultRef, fieldContainer
                    .getClassName(), this.fieldId.getFieldName()));
            }

            newState.getCurrentStackFrame().popOperandStack();
            // push the result of the read operation on the stack
            newState.getCurrentStackFrame().pushOperandStack(resultRef);
        }

        newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());

        return new Pair<>(newState, info);
    }

    /**
     * Returns whether this opcode accesses a static field.
     * @return <code>true</code> iff this accesses a static field
     */
    public boolean isStatic() {
        return this.accessType == FieldAccessType.STATIC;
    }

    /**
     * @return the type of the access (either write or read)
     */
    public FieldAccessRW getReadWriteType() {
        return this.readWriteType;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final ClassPath cPath = postEval.getClassPath();
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();
        final IClass parsedClass =
            Resolver.resolveClassOrThrow(cPath, this.fieldId.getClassName(), null, this
                .getMethod()
                .getIClass()
                .getType());
        if (parsedClass == null) {
            /*
             * The class was not found. In forward-evaluation, this lead to an
             * exception, so we can just use the clone of postEvalInst and just
             * need to remove the exception stack frame and unset the exception
             * bit.
             */
            preEvalInst.getCallStack().pop();
            preEvalInst.getCurrentStackFrame().unsetException();
            return preEvalInst;
        }
        // If we can't resolve the field, we know what to do
        final Field field =
            Resolver.resolveFieldOrThrow(parsedClass, this.fieldId.getFieldName(), null, this
                .getMethod()
                .getIClass()
                .getType());
        if (field == null) {
            /*
             * The field was not found. In forward-evaluation, this lead to an
             * exception, so we can just use the clone of postEvalInst and just
             * need to remove the exception stack frame and unset the exception
             * bit.
             */
            preEvalInst.getCallStack().pop();
            preEvalInst.getCurrentStackFrame().unsetException();
            return preEvalInst;
        }
        final IClass fieldContainer = cPath.getClass(field.getClassName());

        switch (this.accessType) {
        case STATIC:
            /*
             * Check whether or not the field pointed at in the constant pool
             * is static, otherwise pop the thrown exception:
             */
            final Field staticField = fieldContainer.getStaticFields().get(this.fieldId.getFieldName());
            if (staticField == null) {
                preEvalInst.getCallStack().pop();
                preEvalInst.getCurrentStackFrame().unsetException();
                return preEvalInst;
            }

            if (this.readWriteType == FieldAccessRW.READ) {
                //Just remove the read value:
                curInstFrame.popOperandStack();
            } else {
                // Check if we are allowed to write the field (i.e. that it is not final)
                if (field.isFinal()) {
                    // The only exception here is: The field is declared in the current class,
                    // and the current method is its <clinit>
                    final IMethod method = this.getMethod();
                    if (!method.getIClass().equals(fieldContainer) || !method.isClassInitializer()) {
                        preEvalInst.getCallStack().pop();
                        preEvalInst.getCurrentStackFrame().unsetException();
                        return preEvalInst;
                    }
                }
                /*
                 * Otherwise put the written value on the stack again,
                 * restore the old field value:
                 */
                final ClassName fieldClass = fieldContainer.getClassName();
                final String fieldName = this.fieldId.getFieldName();
                curInstFrame.pushOperandStack(postEvalInst.getStaticFields().get(fieldClass, fieldName));
                preEvalInst.getStaticFields().set(
                    fieldClass,
                    fieldName,
                    State.mapOrCopyRef(
                        preEval,
                        preEvalInst,
                        preEval.getStaticFields().get(fieldClass, fieldName),
                        refMap));

                /*
                 * Reverse the note about changed input references, if needed:
                 */
                for (int frameNum = 0; frameNum < preEval.getCallStack().size(); frameNum++) {
                    final InputReferences preEvalAbstrInputRefs =
                        preEval.getCallStack().get(frameNum).getInputReferences();
                    final InputReferences preEvalInstInputRefs =
                        preEvalInst.getCallStack().get(frameNum).getInputReferences();

                    preEvalInstInputRefs.setUnchanged(fieldId);
                    preEvalAbstrInputRefs.getChangeInformation(fieldId).ifPresent(changeInfo ->
                        preEvalInstInputRefs.getChangedSF().put(fieldId, changeInfo.copy())
                    );
                }
            }
            curInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

            return preEvalInst;
        case INSTANCE:
            /*
             * Check whether or not the field pointed at in the constant pool
             * is an instance field, otherwise pop the thrown exception:
             */
            final Field instanceField = fieldContainer.getInstanceFields().get(this.fieldId.getFieldName());
            if (instanceField == null) {
                preEvalInst.getCallStack().pop();
                preEvalInst.getCurrentStackFrame().unsetException();
                return preEvalInst;
            }

            // Get the reference to access
            final AbstractVariableReference abstrObjectRef;
            if (this.readWriteType == FieldAccess.FieldAccessRW.WRITE) {
                abstrObjectRef = preEval.getCurrentStackFrame().getOperandStack().peek(1);
            } else {
                abstrObjectRef = preEval.getCurrentStackFrame().getOperandStack().peek(0);
            }

            if (this.readWriteType == FieldAccess.FieldAccessRW.WRITE) {
                // Check if we are allowed to write the field (i.e. that it is not final)
                if (field.isFinal()) {
                    // The only exception here is: The field is declared in the current class,
                    // and the current method is one of its <init>s
                    final IMethod method = this.getMethod();
                    if (!method.getIClass().equals(fieldContainer) || !method.isInstanceInitializer()) {
                        preEvalInst.getCallStack().pop();
                        preEvalInst.getCurrentStackFrame().unsetException();
                        return preEvalInst;
                    }
                }
            }
            final AbstractVariableReference instObjectRef =
                State.mapOrCopyRef(preEval, preEvalInst, abstrObjectRef, refMap);

            // Get the matching object
            final ObjectInstance abstrObject = (ObjectInstance) preEval.getAbstractVariable(abstrObjectRef);
            final ObjectInstance instObject = (ObjectInstance) preEvalInst.getAbstractVariable(instObjectRef);

            // Check for nullness
            if (abstrObject.isNULL()) {
                preEvalInst.getCallStack().pop();
                preEvalInst.getCurrentStackFrame().unsetException();
                return preEvalInst;
            }

            /*
             * If we've written a value, push the arguments for putfield back
             * onto the stack and restore the old field value.
             */
            if (this.readWriteType == FieldAccess.FieldAccessRW.WRITE) {
                final ConcreteInstance concrObject = (ConcreteInstance) abstrObject;
                //Get value and field data from the abstract state:
                final AbstractVariableReference abstrValueRef = preEval.getCurrentStackFrame().peekOperandStack(0);
                final AbstractVariableReference abstrFieldRef =
                    concrObject.getField(fieldContainer.getClassName(), this.fieldId.getFieldName());

                //Convert them to references in our instance:
                final AbstractVariableReference instValueRef =
                    State.mapOrCopyRef(preEval, preEvalInst, abstrValueRef, refMap);
                final AbstractVariableReference instFieldRef =
                    State.mapOrCopyRef(preEval, preEvalInst, abstrFieldRef, refMap);

                instObject.putField(
                    null,
                    instObjectRef,
                    fieldContainer.getClassName(),
                    this.fieldId.getFieldName(),
                    instFieldRef);

                //Set reachable types
                preEvalInst.getHeapAnnotations().setReachableTypes(instObjectRef, preEval.getHeapAnnotations().getReachableTypes(abstrObjectRef));

                //Push object and value refs back onto the stack:
                curInstFrame.pushOperandStack(instObjectRef);
                curInstFrame.pushOperandStack(instValueRef);
            } else {
                //Just remove the read value and out the object back onto the stack:
                curInstFrame.popOperandStack();
                curInstFrame.pushOperandStack(instObjectRef);
            }
            break;
        default:
            assert (false) : "Unknown field access type";
            return null;
        }

        curInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

        return preEvalInst;
    }

    /**
     * @return {@link FieldAccess#fieldId}
     */
    public FieldIdentifier getFieldId() {
        return this.fieldId;
    }

    @Override
    public int getNumberOfArguments() {
        switch (accessType) {
            case INSTANCE: {
                switch (readWriteType) {
                    case READ: return 1;
                    case WRITE: return 2;
                    default: throw new RuntimeException();
                }
            }
            case STATIC: {
                switch (readWriteType) {
                    case READ: return 0;
                    case WRITE: return 1;
                    default: throw new RuntimeException();
                }
            }
            default: throw new RuntimeException();
        }
    }

    @Override
    public int getNumberOfOutputs() {
        switch (readWriteType) {
            case READ: return 1;
            case WRITE: return 0;
            default: throw new RuntimeException();
        }
    }

}
