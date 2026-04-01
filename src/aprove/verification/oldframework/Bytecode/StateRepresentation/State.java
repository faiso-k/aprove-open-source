/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.StateRepresentation;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;
import java.util.Map.*;

import org.json.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.runtime.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A state is the representation of every memory information. This includes the
 * stack frames present in the call stack, the heap, information about static
 * fields, ...
 */
public class State implements Cloneable {
    /**
     * The enclosing termination graph.
     */
    private final TerminationGraph termGraph;

    /**
     * The considered class path for this analysis.
     */
    private final ClassPath classPath;

    /**
     * Map from identifiers of abstract variables to the actual abstract
     * variables.
     */
    private Map<AbstractVariableReference, AbstractVariable> abstractVariables;

    /**
     * Object holding the annotations of references in this state's heap.
     */
    private HeapAnnotations annotations;

    /**
     * Call stack leading to this state: One frame for each method invocation,
     * or an abstracted frame representing a number of different invocations.
     */
    private CallStack callStack;

    /**
     * Object holding information about the initialized classes.
     */
    private ClassInitializationInformation classInitInfo;

    /**
     * Is set if the condition of the corresponding opcode has been decided
     * beforehand.
     */
    private SplitResult splitResult;

    /**
     * Values of static fields in this VM instance.
     */
    private StaticFields staticFields;

    /**
     * Information needed to handle the created atomic field updaters.
     */
    private AtomicFieldUpdaterInfo atomicFieldUpdaterInfo;

    /**
     * Set of integer relations we might need.
     */
    private IntegerRelations integerRelations;

    /**
     * Notify these objects if this state is deleted from its graph.
     */
    private Collection<StateDeletionListener> deletionListeners;

    private Map<AbstractVariableReference, String> concreteStrings;

    private Map<AbstractVariableReference, FuzzyType> classInstances;

    /**
     * Creates an empty state that must be filled with information before usage.
     * @param cPath considered class path for this analysis.
     * @param terminationGraph the termination graph to which this state belongs
     */
    public State(final ClassPath cPath, final TerminationGraph terminationGraph) {
        this.termGraph = terminationGraph;
        this.classPath = cPath;
        this.callStack = new CallStack();
        this.classInitInfo = new ClassInitializationInformation();
        this.staticFields = new StaticFields();
        this.abstractVariables = new LinkedHashMap<>();
        this.annotations = new HeapAnnotations();
        this.splitResult = null;
        this.atomicFieldUpdaterInfo = new AtomicFieldUpdaterInfo();
        this.integerRelations = new IntegerRelations();
        this.concreteStrings = new LinkedHashMap<>();
        this.classInstances = new LinkedHashMap<>();
    }

    /**
     * Create a fresh state, starting with the specified method.
     * @param cPath considered class path for this analysis.
     * @param terminationGraph the termination graph to which this state belongs
     * @param method some method
     * @param startStateAnnotator this describes where to put annotations (are the arguments sharing? etc.)
     */
    public State(
        final ClassPath cPath,
        final TerminationGraph terminationGraph,
        final IMethod method,
        final StartStateAnnotator startStateAnnotator)
    {
        this(cPath, terminationGraph);

        final StackFrame topFrame = new StackFrame(method);
        this.callStack.push(topFrame);

        /*
         * This is a hack which is OK, because we know what Object.<clinit>() does: nothing. Without this it is
         * difficult to fill the start state with instances of Object.
         */
        this.classInitInfo.setInitialized(JAVA_LANG_OBJECT.getClassName(), InitStatus.YES);

        final AbstractType anyPossibleReferenceType =
            new AbstractType(cPath, new FuzzyClassType(FuzzyClassType.FT_JAVA_LANG_OBJECT.getMinimalClass(), false));

        final List<AbstractVariableReference> argumentRefs = new ArrayList<>();
        final boolean isStatic = method.isStatic();
        if (!isStatic) {
            // Create a "this" instance that really exists
            final IClass parsedClass = method.getIClass();
            final TypeTree instType = parsedClass.getType();

            ObjectInstance thisInstance = ConcreteInstance.newJLO(this);
            final AbstractVariableReference thisRef = this.createReferenceAndAdd(thisInstance, OperandType.ADDRESS);
            this.annotations.setExistenceIsKnown(thisRef);
            this.getHeapAnnotations().setAbstractType(
                thisRef,
                new AbstractType(cPath, new FuzzyClassType(instType.getClassName(), !instType.hasSubTypes())));
            this.getHeapAnnotations().setReachableTypes(thisRef, anyPossibleReferenceType);
            topFrame.setLocalVariable(0, thisRef);
            final LocVarRootPosition pos = LocVarRootPosition.create(0, 0);
            topFrame.getInputReferences().addArgument(pos, thisRef);

            argumentRefs.add(thisRef);
        }
        final ParsedMethodDescriptor sig = method.getDescriptor();
        int index;
        int sigIndex = 0;
        if (isStatic) {
            index = 0;
        } else {
            index = 1;
        }
        final int sigMax = sig.getArgumentCount();
        while (sigIndex < sigMax) {
            final FuzzyType type = sig.getType(sigIndex);

            final AbstractVariableReference freshVar =
                VariableInitialization.getFreshVarFor(type, null, this, FieldValueSettings.GENERAL_VALUE);
            topFrame.setLocalVariable(index, freshVar);
            final LocVarRootPosition pos = LocVarRootPosition.create(0, index);
            topFrame.getInputReferences().addArgument(pos, freshVar);
            if (type instanceof FuzzyPrimitiveType) {
                final FuzzyPrimitiveType prim = (FuzzyPrimitiveType) type;
                final int words = prim.getPrimitiveType().getWords();
                index += words;
            } else {
                index++;
            }
            sigIndex++;

            argumentRefs.add(freshVar);
        }

        // add more annotations to/between the arguments?
        startStateAnnotator.annotate(this, argumentRefs);
        getJBCOptions().dumpMethodInfoTo().ifPresent(method::dumpMethodInfo);
    }

    /**
     * Add the given variable and reference it using the given reference.
     * @param ref the reference
     * @param var the referenced variable to be added
     */
    public void addAbstractVariable(final AbstractVariableReference ref, final AbstractVariable var) {
        assert (var != null);
        assert (!var.isNULL());
        final AbstractVariable oldVar = this.abstractVariables.get(ref);
        assert (oldVar == null || oldVar.equals(var));
        assert (!ref.pointsToConstantInt() || ref.toLiteralInt().equals(var)) : "Trying to reset ref to constant int to wrong value";
        this.abstractVariables.put(ref, var);
    }

    /**
     * Add the new frame to the stack and clear the opcode counter.
     * @param newFrame the new stack frame.
     */
    public void addFrame(final StackFrame newFrame) {
        this.callStack.push(newFrame);
    }

    /**
     * Add the given reference to this state and take all information from the
     * given state.
     * @param ref some reference
     * @param hasInfo a state with information about the reference
     * @param refMap map from references in <code>hasInfo</code> to references
     *  in <code>this</code.>
     */
    public void addReferenceAndInfo(
        final AbstractVariableReference ref,
        final State hasInfo,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        this.addReferenceAndInfo(ref, hasInfo, refMap, new LinkedHashSet<AbstractVariableReference>());
    }

    /**
     * Add the given reference to this state and take all information from the
     * given state.
     * @param ref some reference
     * @param hasInfo a state with information about the reference
     * @param refMap map from references in <code>hasInfo</code> to references
     *  in <code>this</code>.
     * @param seen a collection of references that are handled already
     */
    public void addReferenceAndInfo(
        final AbstractVariableReference ref,
        final State hasInfo,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final Collection<AbstractVariableReference> seen)
    {
        if (seen.contains(ref)) {
            return;
        }
        seen.add(ref);

        final AbstractVariable oldVar = hasInfo.getAbstractVariable(ref);
        if (oldVar != null) {
            final AbstractVariable var = oldVar.clone();
            this.addAbstractVariable(ref, var);
            if (var instanceof ConcreteInstance) {
                final ConcreteInstance instance = (ConcreteInstance) var;
                ConcreteInstance curInstSlice = instance.getMostSpecializedInstance();
                while (curInstSlice != null) {
                    final Map<String, AbstractVariableReference> fieldMap = curInstSlice.getFields();
                    for (final Entry<String, AbstractVariableReference> entry : fieldMap.entrySet()) {
                        final String fieldName = entry.getKey();
                        final AbstractVariableReference subRef = entry.getValue();
                        /*
                         * Only add new information recursively if we don't know
                         * the reference (either because we already copied it
                         * or because it is already mapped):
                         */
                        if (!seen.contains(subRef) && !refMap.containsKey(subRef) && !subRef.isNULLRef()) {
                            this.addReferenceAndInfo(subRef, hasInfo, refMap, seen);
                        } else {
                            curInstSlice.setField(fieldName, State.mapOrCopyRef(refMap, subRef));
                        }
                    }
                    curInstSlice = curInstSlice.getSuperClassInstance();
                }
            }
            if (var instanceof ConcreteArray) {
                final ConcreteArray array = (ConcreteArray) var;
                for (int idx = 0; idx < array.getLiteralLength(); idx++) {
                    final AbstractVariableReference subRef = array.get(hasInfo, ref, idx);
                    if (!seen.contains(subRef)) {
                        this.addReferenceAndInfo(subRef, hasInfo, refMap, seen);
                    } else {
                        array.put(idx, State.mapOrCopyRef(refMap, subRef));
                    }
                }
            }
        }
        final AbstractVariableReference newRefName = State.mapOrCopyRef(refMap, ref);

        final AbstractType type = hasInfo.annotations.getAbstractType(ref);
        if (type != null) {
            this.annotations.setAbstractType(newRefName, type);
            final AbstractType reachableTypes = hasInfo.annotations.getReachableTypes(ref);
            this.annotations.setReachableTypes(newRefName, reachableTypes);
        }
        if (hasInfo.annotations.isMaybeExisting(ref)) {
            this.annotations.setMaybeExisting(newRefName);
        }
        if (hasInfo.annotations.isPossiblyNonTree(ref)) {
            this.annotations.setPossiblyNonTree(newRefName);
        }
        if (hasInfo.annotations.getCyclicStructures().isCyclic(ref)) {
            this.annotations.getCyclicStructures().add(
                newRefName,
                hasInfo.annotations.getCyclicStructures().getNeededEdgesOf(ref));
        }

        for (final AbstractVariableReference partner : hasInfo.annotations
            .getJoiningStructures()
            .getReferencesWithPartner(ref))
        {
            this.annotations.getJoiningStructures().add(newRefName, State.mapOrCopyRef(refMap, partner));
        }

        for (final TwoRefs twoRefs : hasInfo.annotations.getEqualityGraph().getCollection()) {
            this.annotations.getEqualityGraph().addPossibleEquality(
                this,
                State.mapOrCopyRef(refMap, twoRefs.getRefOne()),
                State.mapOrCopyRef(refMap, twoRefs.getRefTwo()));
        }

        this.concreteStrings.put(ref, hasInfo.getConcreteString(ref));
        this.classInstances.put(ref, hasInfo.getClassInstance(ref));
    }

    private static AbstractVariableReference mapOrCopyRef(
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final AbstractVariableReference ref)
    {
        if (refMap.containsKey(ref)) {
            return refMap.get(ref);
        }
        return ref;
    }

    /**
     * @return true iff the call stack is empty
     */
    public boolean callStackEmpty() {
        return this.callStack.isEmpty();
    }

    /**
     * Returns a deep (!) copy of this {@link State} object.
     * @return Deep copy of this object
     */
    @Override
    public State clone() {
        final State clone = new State(this.classPath, this.termGraph);

        clone.staticFields = this.staticFields.clone();

        clone.abstractVariables = new LinkedHashMap<>();
        for (final Map.Entry<AbstractVariableReference, AbstractVariable> e : this.abstractVariables.entrySet()) {
            clone.abstractVariables.put(e.getKey(), e.getValue().clone());
        }

        clone.annotations = this.annotations.clone();

        clone.callStack = this.callStack.clone();

        // assert that there is no NRIR on the call stack
        if (Globals.useAssertions) {
            final Collection<AbstractVariableReference> nrirs = this.getAllNRIRs();
            if (!nrirs.isEmpty()) {
                final Map<AbstractVariableReference, Integer> references = new DefaultValueMap<>(Integer.valueOf(0));

                this.getCallStack().getTop().getReferences(references, false);
                for (final AbstractVariableReference nrir : nrirs) {
                    assert (!references.keySet().contains(nrir));
                }
            }
        }

        clone.classInitInfo = this.classInitInfo.clone();

        clone.atomicFieldUpdaterInfo = this.atomicFieldUpdaterInfo.clone();

        clone.integerRelations = this.integerRelations.clone();

        clone.concreteStrings.putAll(concreteStrings);
        clone.classInstances.putAll(classInstances);

        return clone;
    }

    /**
     * Create a new reference for the given variable, add this variable with the
     * new reference and return the new reference.
     * @param v some variable
     * @return the new reference
     */
    public AbstractVariableReference createReferenceAndAdd(final AbstractVariable v, final OperandType primType) {
        assert (v != null);
        final AbstractVariableReference ref = AbstractVariableReference.create(v, primType);
        if (!this.abstractVariables.containsKey(ref) && !v.isNULL()) {
            /*
             * For null and constant integers/floats/... we might already have
             * the "same" variable for the reference.
             */
            this.addAbstractVariable(ref, v);
        }
        return ref;
    }

    /**
     * @return object holding annotations of references in this state's heap.
     */
    public HeapAnnotations getHeapAnnotations() {
        return this.annotations;
    }

    /**
     * @return object holding information about the initialized classes.
     */
    public ClassInitializationInformation getClassInitInfo() {
        return this.classInitInfo;
    }

    /**
     * This removes every information from the state that is not "reachable"
     * from the stack or any static field.
     * @return true if any annotation was removed (e.g. because we inferred it
     * is not possible).
     */
    public Pair<Boolean, Set<VariableInformation>> gc() {
        final Set<AbstractVariableReference> toKeep = this.getReferences().keySet();
        final Collection<AbstractVariableReference> toRemove = new LinkedHashSet<>();

        final Collection<AbstractVariableReference> toCheck = new LinkedHashSet<>();
        toCheck.addAll(this.abstractVariables.keySet());
        toCheck.addAll(this.annotations.getReferences());
        for (final AbstractVariableReference id : toCheck) {
            if (!toKeep.contains(id)) {
                toRemove.add(id);
            }
        }

        for (final AbstractVariableReference ref : toKeep) {
            if (ref.pointsToArray()) {
                final AbstractVariable var = this.getAbstractVariable(ref);
                assert (var instanceof Array || this.annotations.isMaybeExisting(ref));
            }
        }

        final Pair<Boolean, Set<VariableInformation>> annotationRemoved = this.annotations.gc(this, toKeep, toRemove);

        for (final AbstractVariableReference id : toRemove) {
            this.abstractVariables.remove(id);
            this.atomicFieldUpdaterInfo.remove(id);
            this.integerRelations.remove(id);
            this.concreteStrings.remove(id);
            this.classInstances.remove(id);
        }

        if (Globals.useAssertions) {
            for (final AbstractVariableReference ref : toKeep) {
                if (ref.pointsToReferenceType()) {
                    assert (ref.isNULLRef() || this.annotations.getAbstractType(ref) != null);
                } else {
                    assert (this.getAbstractVariable(ref) != null);
                }
            }
        }

        return annotationRemoved;
    }

    /**
     * @param vr Abstract variable reference
     * @return abstract variable in the current state
     */
    public AbstractVariable getAbstractVariable(final AbstractVariableReference vr) {
        if (vr.isNULLRef()) {
            return ConcreteInstance.NULL;
        }
        return this.abstractVariables.get(vr);
    }

    /**
     * @return the callStack
     */
    public CallStack getCallStack() {
        return this.callStack;
    }

    /**
     * @return the opcode that should be evaluated next
     */
    public OpCode getCurrentOpCode() {
        if (!this.callStack.isEmpty()) {
            return this.callStack.getTop().getCurrentOpCode();
        }
        return null;
    }

    /**
     * @return the stack frame that is active at the moment
     */
    public StackFrame getCurrentStackFrame() {
        return this.callStack.getTop();
    }

    /**
     * @return the input references
     */
    public InputReferences getInputReferences() {
        return this.getCurrentStackFrame().getInputReferences();
    }

    /**
     * @return the considered class path for this analysis.
     */
    public final ClassPath getClassPath() {
        return this.classPath;
    }

    /**
     * @param pos a state position
     * @return the reference at position pos (this|_pos)
     */
    public AbstractVariableReference getReference(final StatePosition pos) {
        assert (pos != null);
        return pos.getFromState(this);
    }

    /**
     * @return for each abstract variable reference the number the corresponding
     * variable is used inside this state.
     */
    public Map<AbstractVariableReference, Integer> getReferences() {
        return this.getReferences(false);
    }

    /**
     * @param includeIntegerRelations set if occurrences in Interger Relations should be counted as well
     * @return for each abstract variable reference the number the corresponding
     * variable is used inside this state.
     */
    public Map<AbstractVariableReference, Integer> getReferences(boolean includeIntegerRelations) {
        final Map<AbstractVariableReference, Integer> res = new DefaultValueMap<>(0);
        this.callStack.getReferences(res);
        this.staticFields.getReferences(res);

        //Descend into references to instances to get stuff from the heap:
        final Queue<AbstractVariableReference> instancesToCheck = new LinkedList<>(res.keySet());
        this.getReferencesFromHeap(res, instancesToCheck);

        if (includeIntegerRelations) {
            this.getIntegerRelations().getReferences(res);
        }

        return res;
    }

    /**
     * @param res add the known references here
     * @param instancesToCheck recurse into the objets referenced from this set
     */
    public void getReferencesFromHeap(
        final Map<AbstractVariableReference, Integer> res,
        final Queue<AbstractVariableReference> instancesToCheck)
    {
        final Set<AbstractVariableReference> done = new LinkedHashSet<>();

        while (!instancesToCheck.isEmpty()) {
            final AbstractVariableReference varRef = instancesToCheck.poll();
            done.add(varRef);
            final AbstractVariable var = this.getAbstractVariable(varRef);

            if (var instanceof ConcreteInstance && !var.isNULL()) {
                for (final Map.Entry<AbstractVariableReference, Integer> e : ((ConcreteInstance) var)
                    .getFieldValues()
                    .entrySet())
                {
                    final AbstractVariableReference fieldValue = e.getKey();
                    if (fieldValue == null) {
                        continue;
                    }
                    res.put(fieldValue, res.get(fieldValue) + 1);
                    if (!done.contains(fieldValue)) {
                        instancesToCheck.add(fieldValue);
                    }
                }
            } else if (var instanceof Array) {
                for (final Map.Entry<AbstractVariableReference, Integer> e : ((Array) var).getReferences().entrySet()) {
                    final AbstractVariableReference fieldValue = e.getKey();
                    res.put(fieldValue, res.get(fieldValue) + e.getValue());
                    if (!done.contains(fieldValue)) {
                        instancesToCheck.add(fieldValue);
                    }
                }
            }
        }
    }

    /**
     * @return the enforced split result.
     */
    public SplitResult getSplitResult() {
        return this.splitResult;
    }

    /**
     * @return Values of static fields in this VM instance.
     */
    public StaticFields getStaticFields() {
        return this.staticFields;
    }

    /**
     * Replace one reference by another. Take care that the abstract type
     * information of the old references is also copied to the new reference!
     * @param oldRef the reference to be replaced
     * @param newRef the new reference
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        assert (oldRef != null);
        assert (newRef != null);
        if (oldRef.equals(newRef)) {
            return;
        }

        this.replaceReferencesWithoutAnnotations(oldRef, newRef);

        //Also carry over all annotations for instances:
        if (oldRef.pointsToReferenceType()) {
            this.annotations.replaceReference(this, oldRef, newRef);
        }
    }

    /**
     * Replace the reference in the stack, static fields, input references,
     * class instances, and the heap.
     * @param oldRef the old reference
     * @param newRef the new reference
     */
    public void replaceReferencesWithoutAnnotations(
        final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef)
    {
        this.replaceReferenceWithoutHeap(oldRef, newRef);
        this.replaceReferenceInHeap(oldRef, newRef);
    }

    /**
     * Rename the reference in the stack, static fields, input references, and
     * class instances.
     * @param oldRef the old reference
     * @param newRef the new reference
     */
    private void replaceReferenceWithoutHeap(
        final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef)
    {
        this.callStack.replaceReference(oldRef, newRef);
        this.staticFields.replaceReference(oldRef, newRef);
        this.atomicFieldUpdaterInfo.replaceReference(oldRef, newRef);
        if (concreteStrings.containsKey(oldRef)) {
            setConcreteString(newRef, this.concreteStrings.get(oldRef));
        }
        this.concreteStrings.remove(oldRef);
        this.classInstances.put(newRef, this.classInstances.get(oldRef));
        this.classInstances.remove(oldRef);
        this.integerRelations.replaceReference(oldRef, newRef);

    }

    /**
     * Replace the reference everwhere it is mentioned in the heap.
     * @param oldRef the old reference
     * @param newRef the new reference
     */
    private void replaceReferenceInHeap(final AbstractVariableReference oldRef, final AbstractVariableReference newRef)
    {
        //Also replace stuff on the heap:
        for (final AbstractVariable v : this.abstractVariables.values()) {
            if (v instanceof ConcreteInstance) {
                final ConcreteInstance aI = (ConcreteInstance) v;
                aI.replaceReference(oldRef, newRef);
            }
            if (v instanceof Array) {
                final Array aA = (Array) v;
                aA.replaceReference(oldRef, newRef);
            }
        }
    }

    /**
     * Record that variable points to an instance which is of the given abstract
     * type.
     * @param ref {@link AbstractVariableReference} to record the class of.
     * @param type of the variable referenced by ref.
     */
    public void setAbstractType(final AbstractVariableReference ref, final AbstractType type) {
        assert (type != null);
        if (ref.isNULLRef() || (this.getAbstractVariable(ref) != null && this.getAbstractVariable(ref).isNULL())) {
            assert (false);
        }
        this.annotations.setAbstractType(ref, type);
    }

    /**
     * Set the OpCode in the current stack frame.
     * @param opCode the opcode
     */
    public void setCurrentOpCode(final OpCode opCode) {
        this.callStack.getTop().setCurrentOpCode(opCode);
    }

    /**
     * @param r the enforced split result.
     */
    public void setSplitResult(final SplitResult r) {
        this.splitResult = r;
    }

    /**
     * @return a readable string representation of the state.
     */
    @Override
    public String toString() {
        return this.toString(false, false);
    }

    /**
     * @param pretty iff true we will drop all of the internal stuff.
     * @return a readable string representation of the state
     */
    public String toString(final boolean pretty) {
        return this.toString(pretty, false);
    }

    /**
     * @param pretty iff true we will drop all of the internal stuff.
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return a readable string representation of the state
     */
    public String toString(final boolean pretty, final boolean shortRepresentation) {
        if (this.callStackEmpty()) {
            return "END";
        }
        final StringBuilder t = new StringBuilder();
        if (!pretty && Globals.DEBUG_COTTO) {
            t.append(this.hashCode());
            t.append("\n");
        }

        if (this.splitResult != null) {
            this.splitResult.toString(t);
            t.append("\n");
        }

        /*
         * get a list of variable users, so that we can put values right into
         * place when they are used only there
         */
        final Map<AbstractVariableReference, Integer> varUsers = this.getReferences(true);

        // call Stack
        t.append(this.callStack.toString(varUsers, this, shortRepresentation));
        t.append("\n");

        // static Fields
        t.append(this.staticFields.toString(varUsers, this, shortRepresentation));

        // abstract Variables
        for (final Map.Entry<AbstractVariableReference, AbstractVariable> e : this.abstractVariables.entrySet()) {
            final AbstractVariable v = e.getValue();
            if (v instanceof AbstractInt && ((AbstractInt) v).isLiteral() || v.isNULL()) {
                continue;
            }
            final AbstractVariableReference varId = e.getKey();
            //Only print it here if the variable is used more than once:

            if (!shortRepresentation || varUsers.get(varId) > 1 || v instanceof ObjectInstance || v instanceof Array) {
                final AbstractType type = this.annotations.getAbstractType(varId);
                if (type != null) {
                    if (v instanceof ConcreteInstance) {
                        final ConcreteInstance ai = (ConcreteInstance) v;
                        t.append("\t").append(varId);
                        final FuzzyClassType minimalClass = type.getMinimalClass();

                        if (minimalClass != null
                            && minimalClass.isConcrete()
                            && minimalClass.getMinimalClass().equals(
                                ai.getMostSpecializedInstance().getType().getClassName()))
                        {
                            t.append("!");
                        } else {
                            t.append("(").append(type.toString()).append(")");
                        }
                    } else if (v instanceof Array || v instanceof AbstractInstance) {
                        t.append("\t").append(varId).append("(").append(type).append(")");
                    } else {
                        assert (false) : "Unknown non-primitive value";
                    }
                } else {
                    t.append("\t").append(varId);
                }
                if (this.annotations.isPossiblyNonTree(varId)) {
                    if (this.annotations.getCyclicStructures().isCyclic(varId)
                        && this.annotations.getCyclicStructures().getNeededEdgesOf(varId).isEmpty())
                    {
                        t.append(" @[]");
                    } else {
                        t.append(" <>");
                    }
                }
                t.append(": ");
                if (v instanceof ConcreteInstance) {
                    t.append(((ConcreteInstance) v).toString(varUsers, this, shortRepresentation));
                } else if (v instanceof Array) {
                    t.append(((Array) v).toString(varId, varUsers, this, shortRepresentation));
                } else {
                    t.append(v.toString());
                }

                final AbstractType reachableTypes = this.annotations.getReachableTypes(varId);
                if (reachableTypes != null) {
                    t.append(" -->{");
                    reachableTypes.toString(t);
                    t.append("}");
                }

                t.append("\n");
            }
        }

        // for maybe-existing variables also print the type information
        for (final AbstractVariableReference ref : this.annotations.getMaybeExistingInstances()) {
            final AbstractType abstractType = this.annotations.getAbstractType(ref);
            t.append(ref);
            t.append(":: ");
            t.append(abstractType);
            if (this.annotations.isPossiblyNonTree(ref)) {
                if (this.annotations.getCyclicStructures().isCyclic(ref)
                    && this.annotations.getCyclicStructures().getNeededEdgesOf(ref).isEmpty())
                {
                    t.append(" @[]");
                } else {
                    t.append(" <>");
                }
            }

            final AbstractType reachableTypes = this.annotations.getReachableTypes(ref);
            if (reachableTypes != null) {
                t.append(" -->{" + reachableTypes + "}");
            }
            t.append("\n");
        }

        // annotations
        this.annotations.getEqualityGraph().toString(t);
        this.annotations.getCyclicStructures().toString(t, false);
        this.annotations.getJoiningStructures().toString(t);

        final Collection<String> treeSet = new TreeSet<>();
        for (final DefiniteReachabilityAnnotation defReach : this.annotations.getDefiniteReachabilities()) {
            treeSet.add(defReach.toString() + "\n");
        }
        for (final String string : treeSet) {
            t.append(string);
        }

        this.annotations.getArrayInfo().toString(t);

        // initialized classes
        this.classInitInfo.toString(t, this.getClassPath(), this.getJBCOptions());

        // relations
        if (!pretty && !this.integerRelations.isEmpty()) {
            t.append("Relations: ").append(this.integerRelations.toString());
        }

        return t.toString();
    }

    /**
     * Remove the variable information for the given reference.
     * @param ref some reference
     */
    public void removeAbstractVariable(final AbstractVariableReference ref) {
        this.abstractVariables.remove(ref);
    }

    /**
     * Fill this state will all data found in the other state. This may be less
     * useful in case the two states have common references.
     * @param otherState the state to copy from
     */
    public void addAllDataFrom(final State otherState) {
        for (final AbstractVariableReference ref : otherState.getReferences().keySet()) {
            if (ref.isNULLRef()) {
                continue;
            }
            if (ref instanceof ReturnAddress) {
                continue;
            }
            final AbstractVariable var = otherState.getAbstractVariable(ref);
            if (var != null) {
                this.addAbstractVariable(ref, var.clone());
            }
            this.annotations.addAllDataFrom(this, otherState.getHeapAnnotations(), ref);
            this.concreteStrings.put(ref, otherState.getConcreteString(ref));
            this.classInstances.put(ref, otherState.getClassInstance(ref));
        }
    }

    /**
     * @param ref a reference
     * @return true only if the referenced object is fully realized (no new
     * field/array element may be introduced due to refinement)
     */
    public boolean isFullyRealized(final AbstractVariableReference ref) {
        if (this.annotations.isMaybeExisting(ref)) {
            return false;
        }
        final AbstractType at = this.annotations.getAbstractType(ref);
        if (!at.isConcrete()) {
            return false;
        }
        final AbstractVariable var = this.getAbstractVariable(ref);
        if (var instanceof ConcreteInstance) {
            final ConcreteInstance ai = (ConcreteInstance) var;
            //at is concrete, so only contains one type which is not fuzzy. Get it:
            final FuzzyType ft = at.getPossibleClassesCopy().iterator().next();
            if (ft.isArrayType()) {
                return false;
            } else if (!ai
                .getMostSpecializedInstance()
                .getType()
                .getClassName()
                .equals(((FuzzyClassType) ft).getMinimalClass()))
            {
                return false;
            }
            // maybe there is some non-realized field inside an otherwise realized slice?
            ConcreteInstance current = ((ConcreteInstance) var).getMostSpecializedInstance();
            while (current != null) {
                if (current.hasUnrealizedField()) {
                    return false;
                }
                current = current.getSuperClassInstance();
            }
        } else if (!(var instanceof ConcreteArray)) {
            return false;
        }
        return true;
    }

    /**
     * @return the enclosing termination graph.
     */
    public TerminationGraph getTerminationGraph() {
        return this.termGraph;
    }

    /**
     * @param ref {@link AbstractVariableReference} to return type information
     * for.
     * @return type information about var
     */
    public AbstractType getAbstractType(final AbstractVariableReference ref) {
        return this.annotations.getAbstractType(ref);
    }

    /**
     * @return the information needed to handle the created atomic field updaters.
     */
    public AtomicFieldUpdaterInfo getAtomicFieldUpdaterInfo() {
        return this.atomicFieldUpdaterInfo;
    }

    /**
     * @param infoSource some state from which info needs to be taken if the
     *  reference in question is not contained in <code>refMap</code> and
     *  <code>infoTarget</code>
     * @param infoTarget state into which the information is to be stored
     *  if it's not already there.
     * @param refToMapOrCopy some reference known in <code>infoSource</code>
     * @param refMap a map from references in <code>infoSource</code> to their
     *  counterparts in <code>infoTarget</code>
     * @return name of a reference pointing to the right content.
     */
    public static AbstractVariableReference mapOrCopyRef(
        final State infoSource,
        final State infoTarget,
        final AbstractVariableReference refToMapOrCopy,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final AbstractVariableReference res;

        //Special cases:
        if (refToMapOrCopy == null) {
            return null;
        } else if (refToMapOrCopy.isNULLRef()) {
            return refToMapOrCopy;
        }

        if (refMap.containsKey(refToMapOrCopy)) {
            res = refMap.get(refToMapOrCopy);
        } else {
            res = refToMapOrCopy;
            infoTarget.addReferenceAndInfo(
                refToMapOrCopy,
                infoSource,
                refMap,
                new LinkedHashSet<AbstractVariableReference>());
            refMap.put(refToMapOrCopy, res);
        }

        return res;
    }

    /**
     * Replace all references by fresh ones (except those referencing
     * constants).
     * @return the applied substitution
     */
    public BidirectionalMap<AbstractVariableReference, AbstractVariableReference> replaceAllReferences() {
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> result = new BidirectionalMap<>();
        for (final AbstractVariableReference ref : this.getReferences().keySet()) {
            if (ref.pointsToConstant()) {
                continue;
            }
            final AbstractVariableReference newRef = AbstractVariableReference.create(ref);
            this.replaceReference(ref, newRef);
            result.putLR(ref, newRef);
            final AbstractVariable oldVar = this.abstractVariables.get(ref);
            if (oldVar != null) {
                this.abstractVariables.put(newRef, oldVar);
            }
        }
        return result;
    }

    /**
     * For a given reference, check some basic information to determine whether
     * the referenced instance can have fields.
     * @param ref a reference (can be null)
     * @return false only if we are sure that the reference does not point to an
     * instance/array with fields/entries (i.e. because it is maybe existing,
     * just jlO or an abstract instance).
     */
    public boolean canHaveFields(final AbstractVariableReference ref) {
        if (ref == null) {
            return false;
        }
        final AbstractVariable var = this.getAbstractVariable(ref);
        if (var == null) {
            return false;
        }
        if (var instanceof AbstractInstance) {
            return false;
        }
        if (var instanceof ConcreteInstance) {
            final ConcreteInstance ai = (ConcreteInstance) var;
            return !ai.isOnlyRealizedUpToJLO();
        }
        return true;

    }

    /**
     * @return the NRIRs in all stack frames
     */
    public Collection<AbstractVariableReference> getAllNRIRs() {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final StackFrame sf : this.callStack.getStackFrameList()) {
            result.addAll(sf.getInputReferences().getNRIRs());
        }
        return result;
    }

    /**
     * @return the integer relations holding in this state.
     */
    public IntegerRelations getIntegerRelations() {
        return this.integerRelations;
    }

    /**
     * A new state is created in which the values of references appearing in <code>refsToAbstractAway</code> have been
     * replaced by abstracted values. To make sure the annotations reflect this, we merged with the original state.
     *
     * @param refsToAbstractAway the references to abstract
     * @param useAbstractInstance if true, we use an {@ref AbstractInstance} to replace the old value. Otherwise,
     *  we just use an unrealized {@ref ConcreteInstance}
     * @return an abstraction of <code>state</code> where references in <code>refsToAbstractAway</code> now point
     *  to abstract values or null if this failed, the new state is the same as the old one or
     *  <code>refsToAbstractAway</code> contained references to primitives.
     */
    public State replaceConcreteInstancesByAbstractedInstance(
        final Collection<AbstractVariableReference> refsToAbstractAway,
        final boolean useAbstractInstance)
    {
        if (refsToAbstractAway.size() == 0) {
            return null;
        }

        final State clone = this.clone();

        final Collection<Triple<AbstractVariableReference, Set<HeapEdge>, AbstractVariableReference>> addMe =
            new LinkedHashSet<>();
        final Map<AbstractVariableReference, AbstractVariableReference> rename = new LinkedHashMap<>();

        // abstract
        for (final AbstractVariableReference ref : refsToAbstractAway) {
            if (!ref.pointsToReferenceType()) {
                return null;
            }

            clone.removeAbstractVariable(ref);
            final AbstractVariable newValue;
            if (useAbstractInstance) {
                newValue = new AbstractInstance();
            } else {
                newValue = ConcreteInstance.newJLO(clone);
            }
            final AbstractVariableReference newRef = clone.createReferenceAndAdd(newValue, OperandType.ADDRESS);
            rename.put(ref, newRef);
            clone.replaceReference(ref, newRef);
        }

        // retain definite reachability information
        for (final AbstractVariableReference ref : refsToAbstractAway) {
            if (!ref.pointsToReferenceType()) {
                return null;
            }

            /*
             * We abstract "ref". If there is some successor "reached", for example ref.f.f.f = reached and we have
             * reached -F!-> x, we add ref -F!-> x if there is a path from ref to reached that only uses fields from F.
             */
            final Collection<AbstractVariableReference> reachRefs = Reachability.getReachableRefs(ref, false, this);
            for (final DefiniteReachabilityAnnotation defReach : this.getHeapAnnotations().getDefiniteReachabilities())
            {
                if (reachRefs.contains(defReach.getFrom())) {
                    final AbstractVariableReference reached =
                        Reachability.followFields(ref, defReach.getFields(), defReach.getFrom(), false, this);
                    if (defReach.getFrom().equals(reached)) {
                        addMe.add(new Triple<>(ref, defReach.getFields(), defReach.getTo()));
                    }
                }
            }

            /*
             * After the abstraction, we do not have the fields of ref anymore. For ref.f = x and ref.f.f = y we add
             * ref -{f}!!-> x and ref -{f}!!-> y. If we manage to reach ref again, we might also add ref -{f}!!-> ref.
             */
            /*
             * TODO find all reachable references (do not consider the fields used to reach these) and then try to find
             * a set of fields that can be used to describe this path. This might find more connections than the current
             * implementation.
             */
            final AbstractVariable var = this.getAbstractVariable(ref);
            if (var instanceof ConcreteInstance) {
                final ConcreteInstance cI = (ConcreteInstance) var;
                for (final FieldIdentifier fieldIdentifier : cI.getAllFields().keySet()) {
                    final HeapEdge heapEdge = new InstanceFieldEdge(fieldIdentifier);
                    final Collection<AbstractVariableReference> reachedRefs =
                        Reachability.followFields(ref, Collections.singleton(heapEdge), this);
                    for (final AbstractVariableReference reachedRef : reachedRefs) {
                        if (reachedRef.equals(ref)) {
                            /*
                             * We reached ref again (of course...), but is it also possible to have a proper cycle with
                             * at least one edge?
                             */
                            if (ref.equals(Reachability.followFields(
                                ref,
                                Collections.singleton(heapEdge),
                                ref,
                                true,
                                this)))
                            {
                                addMe.add(new Triple<>(ref, Collections.singleton(heapEdge), reachedRef));
                            }
                        } else {
                            addMe.add(new Triple<>(ref, Collections.singleton(heapEdge), reachedRef));
                        }
                    }
                }
            }
        }

        for (final Triple<AbstractVariableReference, Set<HeapEdge>, AbstractVariableReference> triple : addMe) {
            AbstractVariableReference from = triple.x;
            if (rename.containsKey(from)) {
                from = rename.get(from);
            }
            if (clone.getHeapAnnotations().isMaybeExisting(from) || from.isNULLRef() || !from.pointsToReferenceType()) {
                continue;
            }
            AbstractVariableReference to = triple.z;
            if (rename.containsKey(to)) {
                to = rename.get(to);
            }
            if (clone.getHeapAnnotations().isMaybeExisting(to) || to.isNULLRef() || !to.pointsToReferenceType()) {
                continue;
            }

            clone
                .getHeapAnnotations()
                .getDefiniteReachabilities()
                .add(new DefiniteReachabilityAnnotation(from, to, triple.y, true, this.classPath));
        }

        final JBCMerger merger = new PathMerger(clone, null);
        clone.gc();
        if (merger.merge(this)) {
            final JBCMergeResult mergeResult = merger.getResult();
            if (mergeResult.partnerEqualsMergedState()) {
                return null;
            }
            return mergeResult.getMergedState();
        }

        return null;
    }

    /**
     * Initialize the set containing the listeners
     */
    public void initializeDeletionListeners() {
        this.deletionListeners = new LinkedHashSet<>();
    }

    /**
     * Notify the objects that wait for the state to be deleted.
     */
    public void notifyDeletionListeners() {
        if (this.deletionListeners != null) {
            for (final StateDeletionListener listener : this.deletionListeners) {
                listener.notifyStateDeletion(this);
            }
            this.deletionListeners = null;
        }
    }

    /**
     * @param listener the object to notify when deleting this state
     */
    public boolean addDeletionListener(final StateDeletionListener listener) {
        if (this.deletionListeners == null) {
            return false;
        }
        this.deletionListeners.add(listener);
        return true;
    }

    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();

        if (this.splitResult != null) {
            res.put("Split Result", this.splitResult.toJSON());
        }
        res.put("Call Stack", this.callStack.toJSON());

        final JSONArray intRelations = this.integerRelations.toJSON();
        final JSONObject heapInformation = new JSONObject();
        for (final Entry<AbstractVariableReference, AbstractVariable> e : this.abstractVariables.entrySet()) {
            AbstractVariableReference ref = e.getKey();
            AbstractVariable val = e.getValue();
            if (val instanceof AbstractNumber) {
                AbstractNumber num = (AbstractNumber) val;
                for (final String sexp : num.toSExpStrings(ref)) {
                    intRelations.put(sexp);
                }
            } else if (val instanceof Array) {
                heapInformation.put(ref.toString(), ((Array) val).toJSON());
            } else if (val instanceof ObjectInstance) {
                heapInformation.put(ref.toString(), ((ObjectInstance) val).toJSON());
            } else {
                throw new NotYetImplementedException("JSON export of " + val.getClass().toString() + " not implemented yet.");
            }
        }
        res.put("Integer Relations", intRelations);
        res.put("Heap Information", heapInformation);

        res.put("Static Fields", this.staticFields.toJSON());

        res.put("Annotations", this.annotations.toJSON());

        return res;
    }

    public Map<AbstractVariableReference, String> getConcreteStrings() {
        return concreteStrings;
    }

    public String getConcreteString(AbstractVariableReference ref) {
        return concreteStrings.get(ref);
    }

    public FuzzyType getClassInstance(AbstractVariableReference ref) {
        return classInstances.get(ref);
    }

    public Map<AbstractVariableReference, FuzzyType> getClassInstances() {
        return classInstances;
    }

    public void setConcreteString(AbstractVariableReference ref, String s) {
        concreteStrings.put(ref, s);
    }

    public void setClassInstance(AbstractVariableReference ref, FuzzyType s) {
        classInstances.put(ref, s);
    }

    private boolean checkIntegerRelationInState(final JBCIntegerRelation relToCheck) {
        AbstractInt leftInt;
        if (relToCheck.leftIntegerIsNoRef()) {
            leftInt = relToCheck.getLeftInt();
        } else {
            AbstractVariableReference leftRef = relToCheck.getLeftIntRef();
            leftInt = (AbstractInt) getAbstractVariable(leftRef);
        }
        if (leftInt == null) {
            return false;
        }
        AbstractInt rightInt;
        if (relToCheck.rightIntegerIsNoRef()) {
            rightInt = relToCheck.getRightInt();
        } else {
            AbstractVariableReference rightRef = relToCheck.getRightIntRef();
            rightInt = (AbstractInt) getAbstractVariable(rightRef);
        }
        if (rightInt == null) {
            return false;
        }
        IntegerRelationType relType = relToCheck.getRelationType();

        boolean sameRef;
        if (relToCheck.leftIntegerIsNoRef() || relToCheck.rightIntegerIsNoRef()) {
            sameRef = false;
        } else {
            sameRef = relToCheck.getLeftIntRef().equals(relToCheck.getRightIntRef());
        }

        boolean relHolds = AbstractInt.computeComparisonResult(relType, leftInt, rightInt, sameRef, false);

        return relHolds;
    }

    public boolean checkIntegerRelation(final JBCIntegerRelation relToCheck) {
        return checkIntegerRelationInState(relToCheck) || getIntegerRelations().implies(relToCheck);
    }

    public boolean note(AbstractVariableReference xR, IntegerRelationType rel, AbstractVariableReference yR) {
        return integerRelations.note(xR, rel, yR);
    }

    public boolean checkIntegerRelation(AbstractVariableReference xR,
            IntegerRelationType rel,
            AbstractVariableReference yR) {
        return checkIntegerRelation(new JBCIntegerRelation(xR, rel, yR));
    }

    public boolean noteNewRefInRelation(AbstractVariableReference newRef, AbstractVariableReference oldRef, int diff) {
        return integerRelations.noteNewRefInRelation(newRef, oldRef, diff);
    }

    public JBCOptions getJBCOptions() {
        return termGraph.getJBCOptions();
    }
}
