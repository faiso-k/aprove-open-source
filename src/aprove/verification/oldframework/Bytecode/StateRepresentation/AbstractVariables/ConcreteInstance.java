package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.util.*;
import java.util.Map.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Concrete representation of instances in our symbolic interpretation.
 * @author Marc Brockschmidt
 */
public final class ConcreteInstance extends ObjectInstance {
    /**
     * This specifies what to put into the fields of new objects.
     */
    public enum FieldValueSettings {
        /**
         * null or 0
         */
        DEFAULT_VALUE,

        /**
         * Themost general value for a given type (used for unknown input)
         */
        GENERAL_VALUE,

        /**
         * Just add the java null reference (i.e., nothing). Do not confuse this with the AbstractVariableReference
         * null!
         */
        NULL_VALUE;
    }

    /**
     * The special null pointer
     */
    public static final ConcreteInstance NULL = new ConcreteInstance();

    /**
     * The fields of this ConcreteInstance.
     */
    private SortedMap<String, AbstractVariableReference> fields;

    /**
     * The most specialized sub-class.
     */
    private ConcreteInstance mostSpecializedClass;

    /**
     * An object representing more specialized instance properties of this
     * class.
     */
    private ConcreteInstance subClassInstance;

    /**
     * An instance of the super-class of this element (null iff this is a
     * java.lang.Object instance).
     */
    private ConcreteInstance superClassInstance;

    /**
     * The type of this ConcreteInstance.
     */
    private final TypeTree type;

    /**
     * This constructor is only used to create the special NULL instance.
     */
    private ConcreteInstance() {
        this.type = null;
        this.fields = new TreeMap<>();
    }

    /**
     * Constructs an ConcreteInstance of the specified class.
     * @param curState state in which this instance is created (needed to create
     * variables representing attributes)
     * @param myRef the enclosing existing reference, if one exists
     * @param instanceType class name for this instance
     * @param doRecursiveCreation indicates whether parent types
     * ("enclosing boxes") should be created recursively.
     * @param fieldValueSettings indicates whether fields of this
     * instance should be created with the default value as specified in the
     * JVMS, or with the most general value for a given type (used for unknown
     * input). For primitives a corresponding AbstractVariable is created. For
     * references, the resulting references must be annotated according to the
     * annotations of "this".
     */
    private ConcreteInstance(
        final State curState,
        final AbstractVariableReference myRef,
        final TypeTree instanceType,
        final boolean doRecursiveCreation,
        final FieldValueSettings fieldValueSettings)
    {
        this(curState, myRef, instanceType, doRecursiveCreation, fieldValueSettings, null);

    }

    /**
     * Constructs an ConcreteInstance of the specified class.
     * @param curState state in which this instance is created (needed to create
     * variables representing attributes)
     * @param myRef the enclosing existing reference, if one exists
     * @param instanceType class name for this instance
     * @param doRecursiveCreation indicates whether parent types
     * ("enclosing boxes") should be created recursively.
     * @param fieldValueSettings indicates whether fields of this
     * instance should be created with the default value as specified in the
     * JVMS, or with the most general value for a given type (used for unknown
     * input). For primitives a corresponding AbstractVariable is created. For
     * references, the resulting references must be annotated according to the
     * annotations of "this".
     * @param mostSpecialized for the new instance store that the most special
     * instance is the given instance.
     */
    private ConcreteInstance(
        final State curState,
        final AbstractVariableReference myRef,
        final TypeTree instanceType,
        final boolean doRecursiveCreation,
        final FieldValueSettings fieldValueSettings,
        final ConcreteInstance mostSpecialized)
    {
        assert (instanceType != null) : "ConcreteInstances need a Type";
        this.mostSpecializedClass = mostSpecialized;
        this.type = instanceType;
        this.fields = new TreeMap<>();

        final InitStatus wasInitialized =
            curState.getClassInitInfo().getInitializationState(instanceType.getClassName(), curState.getJBCOptions());
        assert (wasInitialized == InitStatus.YES || wasInitialized == InitStatus.RUNNING) : instanceType.getClassName()
            + " not initialized!";

        if (instanceType.hasSuperType()) {
            // this is not jlO
            final IClass cls = curState.getClassPath().getClass(instanceType.getClassName());

            // Create values for the fields
            for (final Map.Entry<String, Field> p : cls.getInstanceFields().entrySet()) {
                final AbstractVariableReference newRef =
                    ConcreteInstance.getNewFieldValue(p.getValue(), curState, myRef, fieldValueSettings);
                this.fields.put(p.getKey(), newRef);
            }

            if (doRecursiveCreation) {
                ConcreteInstance mostSpecial;
                if (this.mostSpecializedClass == null) {
                    mostSpecial = this;
                } else {
                    mostSpecial = this.mostSpecializedClass;
                }

                this.superClassInstance =
                    new ConcreteInstance(
                        curState,
                        myRef,
                        instanceType.getSuperType(),
                        true,
                        fieldValueSettings,
                        mostSpecial);
                this.superClassInstance.setSubClassInstance(this);
            }
        }
    }

    /**
     * For the given field, construct a new value based on fieldValueSettings.
     * @param field the field for which we want to create the reference
     * @param state the state in which this happens
     * @param parentRef the reference of the object containing the field, may be null
     * @param fieldValueSettings indicates whether the field should be created with the default value as specified in the
     * JVMS, or with the most general value for a given type (used for unknown input). For primitives a corresponding
     * AbstractVariable is created. For references, the resulting references must be annotated according to the
     * annotations of "this".
     * @return the new reference
     */
    private static AbstractVariableReference getNewFieldValue(
        final Field field,
        final State state,
        final AbstractVariableReference parentRef,
        final FieldValueSettings fieldValueSettings)
    {
        final FuzzyType fuzzyType = FuzzyType.parseTypeDescriptor(field.getDescriptor());
        AbstractVariableReference newRef =
            VariableInitialization.getFreshVarFor(fuzzyType, parentRef, state, fieldValueSettings);
        //If the type intersection is empty, replace it by NULL:
        if (newRef != null
            && newRef.pointsToReferenceType()
            && state.getHeapAnnotations().getAbstractType(newRef) == null)
        {
            newRef = AbstractVariableReference.NULLREF;
        }
        return newRef;
    }

    /**
     * Constructs an ConcreteInstance slice of the specified class. No variables
     * are set, no parent class are created. This is mostly useless without
     * quite a lot of work.
     * @param instanceType class name for this instance
     */
    private ConcreteInstance(final TypeTree instanceType) {
        this.type = instanceType;
        this.fields = new TreeMap<>();
    }

    /**
     * @return The default value defined in the JVMS for this value type
     */
    public static AbstractVariable getDefaultValue() {
        return ConcreteInstance.NULL;
    }

    /**
     * Constructs an ConcreteInstance of the specified class.
     * @param curState state in which this instance is created (needed to create
     * variables representing attributes)
     * @param instanceType class name for this instance
     * @param fieldValueSettings indicates whether fields of this
     * instance should be created with the default value as specified in the
     * JVMS, or with the most general value for a given type (used for unknown
     * input)
     * @return outermost object representing this instance
     */
    public static ConcreteInstance newInstanceFromType(
        final State curState,
        final TypeTree instanceType,
        final FieldValueSettings fieldValueSettings)
    {
        final ConcreteInstance t = new ConcreteInstance(curState, null, instanceType, true, fieldValueSettings);

        return t.getObjectInstance();
    }

    /**
     * Constructs an ConcreteInstance slice of the specified class. No variables
     * are set, no parent class are created. This is mostly useless without
     * quite a lot of work.
     * @param instanceType class name for this instance
     * @return an concrete instance of the specified type, and nothing else
     */
    public static ConcreteInstance newInstanceSliceType(final TypeTree instanceType) {
        return new ConcreteInstance(instanceType);
    }

    /**
     * Returns a deep (!) copy of this {@link ConcreteInstance} object
     * @return Deep copy of this object
     */
    @Override
    public ConcreteInstance clone() {
        assert (this.superClassInstance == null);
        return this.privateClone(null);
    }

    /**
     * Returns the pointer to the {@link ConcreteInstance} object corresponding
     * to <code>typeOfInterest</code>
     * @param typeOfInterest type for which the concrete instance slice should
     * be returned
     * @return {@link ConcreteInstance} object with the correct type
     */
    public ConcreteInstance getConcreteInstanceSliceAtType(final ClassName typeOfInterest) {
        ConcreteInstance curInst = this.getMostSpecializedInstance();
        while (curInst != null && !curInst.getType().getClassName().equals(typeOfInterest)) {
            curInst = curInst.getSuperClassInstance();
        }

        return curInst;
    }

    /**
     * Returns the pointer to the {@link ConcreteInstance} object corresponding
     * to <code>typeOfInterest</code>
     * @param typeOfInterest type for which the concrete instance slice should
     * be returned
     * @return {@link ConcreteInstance} object with the correct type
     */
    public ConcreteInstance getConcreteInstanceSliceAtType(final TypeTree typeOfInterest) {
        return this.getConcreteInstanceSliceAtType(typeOfInterest.getClassName());
    }

    /**
     * @return a map with all fields of this type and its sub types
     */
    public Map<FieldIdentifier, AbstractVariableReference> getAllFields() {
        final Map<FieldIdentifier, AbstractVariableReference> map = new LinkedHashMap<>();
        ConcreteInstance slice = this;
        while (slice != null) {
            for (final Map.Entry<String, AbstractVariableReference> entry : slice.getFields().entrySet()) {
                final FieldIdentifier fieldIdentifier =
                    new FieldIdentifier(slice.getType().getClassName(), entry.getKey());
                map.put(fieldIdentifier, entry.getValue());
            }
            slice = slice.getSubClassInstance();
        }
        return map;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getField(
        final State state,
        final AbstractVariableReference myRef,
        final ClassName className,
        final String name)
    {
        return this.getField(className, name);
    }

    /**
     * @param className name of the class in which to get the field.
     * @param name name of an instance field.
     * @param failOK iff the field does not exist and this is false, an
     * assertion error is thrown
     * @return abstract variable reference to the value of the field
     * <code>name</code>.
     */
    public AbstractVariableReference getField(final ClassName className, final String name, final boolean failOK) {
        ConcreteInstance curInstance = this.getMostSpecializedInstance();
        AbstractVariableReference res = null;

        while (curInstance != null && curInstance.type.isProperSubClassOf(className)) {
            curInstance = curInstance.superClassInstance;
        }
        if (curInstance == null) {
            assert (failOK);
            return null;
        }

        /*
         * We don't need to handle interfaces here, as interface fields are
         * public, static and final (and thus, all accesses are not routed
         * through this method.
         */
        if (curInstance.type.getClassName().equals(className)) {
            while (res == null && curInstance != null) {
                res = curInstance.fields.get(name);
                curInstance = curInstance.superClassInstance;
            }
        }

        if (res == null && !failOK) {
            assert (false) : "Field resolution failed";
        }
        return res;
    }

    /**
     * @param className name of the class in which to get the field.
     * @param name name of an instance field.
     * @return abstract variable reference to the value of the field
     *  <code>name</code>.
     */
    public AbstractVariableReference getField(final ClassName className, final String name) {
        return this.getField(className, name, false);
    }

    /**
     * @return map from field names to values for this concrete instance.
     */
    public Map<String, AbstractVariableReference> getFields() {
        final Map<String, AbstractVariableReference> res = new LinkedHashMap<>();
        for (final Entry<String, AbstractVariableReference> entry : this.fields.entrySet()) {
            if (entry.getValue() == null) {
                continue;
            }
            res.put(entry.getKey(), entry.getValue());
        }
        return res;
    }

    /**
     * @return mapping of abstract variable references to number of uses in this
     * instance.
     */
    public Map<AbstractVariableReference, Integer> getFieldValues() {
        ConcreteInstance curInstance = this.getMostSpecializedInstance();
        final Map<AbstractVariableReference, Integer> res = new DefaultValueMap<>(0);
        while (curInstance != null) {
            for (final AbstractVariableReference r : curInstance.fields.values()) {
                if (r == null) {
                    continue;
                }
                res.put(r, res.get(r) + 1);
            }
            curInstance = curInstance.superClassInstance;
        }
        return res;
    }

    /**
     * @return the mostSpecializedClass
     */
    public ConcreteInstance getMostSpecializedInstance() {
        ConcreteInstance result = this.mostSpecializedClass;
        if (result == null) {
            result = this;
        }
        return result;
    }

    /**
     * @return the instance corresponding to jlO (the least general instance).
     */
    public ConcreteInstance getObjectInstance() {
        if (this.superClassInstance == null) {
            return this;
        }
        return this.superClassInstance.getObjectInstance();
    }

    /**
     * @return all references that are field values (this includes fields of
     * subclasses, as object itself does not have fields).
     */
    public Collection<AbstractVariableReference> getReferences() {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        ConcreteInstance currentInst = this;
        while (currentInst != null) {
            result.addAll(currentInst.fields.values());
            result.remove(null);
            currentInst = currentInst.subClassInstance;
        }
        return result;
    }

    /**
     * @return instance of the enclosed subclass
     */
    public ConcreteInstance getSubClassInstance() {
        return this.subClassInstance;
    }

    /**
     * @return the subtype
     */
    public List<TypeTree> getSubTypes() {
        return this.type.getSubTypes();
    }

    /**
     * @return instance of the superclass of this object
     */
    public ConcreteInstance getSuperClassInstance() {
        return this.superClassInstance;
    }

    /**
     * @return the type
     */
    public TypeTree getType() {
        return this.type;
    }

    /**
     * Clone all subclasses recursively.
     * @param newSuper set the superclass instance to the given value
     * @return a clone where all subclass instances are cloned.
     */
    private ConcreteInstance privateClone(final ConcreteInstance newSuper) {
        if (this == ConcreteInstance.NULL) {
            return ConcreteInstance.NULL;
        }

        final ConcreteInstance clone = (ConcreteInstance) super.clone();
        clone.superClassInstance = newSuper;
        if (this.subClassInstance != null) {
            clone.subClassInstance = this.subClassInstance.privateClone(clone);
            clone.mostSpecializedClass = clone.subClassInstance.getMostSpecializedInstance();
        } else {
            clone.mostSpecializedClass = null;
        }

        clone.fields = new TreeMap<>();
        for (final Map.Entry<String, AbstractVariableReference> e : this.fields.entrySet()) {
            if (e.getValue() == null) {
                clone.fields.put(e.getKey(), null);
            } else {
                clone.fields.put(e.getKey(), e.getValue().clone());
            }
        }

        return clone;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<DefiniteReachabilityAnnotationCreation> putField(
        final State state,
        final AbstractVariableReference myRef,
        final ClassName className,
        final String name,
        final AbstractVariableReference varRef)
    {
        assert (varRef != null);
        ConcreteInstance curInstance = this.getMostSpecializedInstance();

        while (curInstance.type.isProperSubClassOf(className)) {
            curInstance = curInstance.superClassInstance;
        }
        assert (curInstance.type.getClassName().equals(className));

        while (!curInstance.fields.containsKey(name)) {
            curInstance = curInstance.superClassInstance;
            if (curInstance == null) {
                break;
            }
        }
        assert (curInstance != null && curInstance.fields.containsKey(name));

        final LinkedHashSet<DefiniteReachabilityAnnotationCreation> newDefReach = new LinkedHashSet<>();
        if (myRef != null
            && state != null
            && (curInstance.fields.get(name) == null || !curInstance.fields.get(name).equals(varRef)))
        {
            final HeapPositions heapPos = new HeapPositions(state);
            for (final StackFrame sf : state.getCallStack().getStackFrameList()) {
                sf.getInputReferences().markInstanceFieldAsChanged(heapPos, myRef, new FieldIdentifier(className, name), varRef, curInstance.fields.get(name));
            }

            final State cloneAfterWrite = state.clone();
            final ConcreteInstance ci = (ConcreteInstance) cloneAfterWrite.getAbstractVariable(myRef);

            ConcreteInstance curInstanceAfter = ci.getMostSpecializedInstance();

            while (curInstanceAfter.type.isProperSubClassOf(className)) {
                curInstanceAfter = curInstanceAfter.superClassInstance;
            }
            assert (curInstanceAfter.type.getClassName().equals(className));

            while (!curInstanceAfter.fields.containsKey(name)) {
                curInstanceAfter = curInstanceAfter.superClassInstance;
                if (curInstanceAfter == null) {
                    break;
                }
            }
            assert (curInstanceAfter != null && curInstanceAfter.fields.containsKey(name));

            curInstanceAfter.fields.put(name, varRef);

            newDefReach.addAll(AnnotationFixups.annotateAsNewConcreteChild(state, myRef, new InstanceFieldEdge(
                className,
                name), varRef, cloneAfterWrite, true));
        }

        curInstance.fields.put(name, varRef);

        while (curInstance != null) {
            curInstance.fields.remove(name + "!cycleJoint");
            curInstance = curInstance.superClassInstance;
        }

        return newDefReach;
    }

    /**
     * Realize all inner (more special) objects of this instance up to typeOfInterest. This also takes care that there
     * is no abstract field up to typeOfInterest.
     * @param curState state in which this instance is created (needed to create
     * variables representing attributes)
     * @param myRef the enclosing existing reference, if one exists
     * @param typeOfInterest type of the Element up to which this object should
     * be realized
     * @return the references created for the fields (or null)
     */
    public Collection<Pair<HeapEdge, AbstractVariableReference>> realizeUpTo(
        final State curState,
        final AbstractVariableReference myRef,
        final TypeTree typeOfInterest)
    {
        final ConcreteInstance mostSpecializedInstance = this.getMostSpecializedInstance();
        if (mostSpecializedInstance.type.equals(typeOfInterest) && !mostSpecializedInstance.hasUnrealizedField()) {
            // nothing to do
            return Collections.emptySet();
        }
        final List<TypeTree> pathFromTypeOfInterestToCurType =
            typeOfInterest.findPathFrom(mostSpecializedInstance.type.getClassName());

        /*
         * The path we got starts at a subtype of the current mostSpecializedClass and continues down to the
         * typeOfInterest. Create all types on the way and set the correct sub/super fields.
         *
         * The path may be empty, meaning that we only have to fill in values for abstract fields.
         */
        final Collection<Pair<HeapEdge, AbstractVariableReference>> newRefs = new LinkedHashSet<>();
        ConcreteInstance curMostSpec = mostSpecializedInstance;
        for (final TypeTree t : pathFromTypeOfInterestToCurType) {
            final ConcreteInstance subInstance =
                new ConcreteInstance(curState, myRef, t, false, FieldValueSettings.GENERAL_VALUE).getObjectInstance();
            for (final Entry<String, AbstractVariableReference> entry : subInstance.getFields().entrySet()) {
                newRefs.add(new Pair<HeapEdge, AbstractVariableReference>(new InstanceFieldEdge(t.getClassName(), entry
                    .getKey()), entry.getValue()));
            }
            curMostSpec.setSubClassInstance(subInstance);
            subInstance.superClassInstance = curMostSpec;
            curMostSpec = subInstance;
        }

        // Now fill in the abstracted fields. There may be abstract fields anywhere in this object!
        ConcreteInstance current = curMostSpec;
        while (current != null) {
            final IClass cls = curState.getClassPath().getClass(current.getType().getClassName());
            for (final Map.Entry<String, AbstractVariableReference> entry : current.fields.entrySet()) {
                if (entry.getValue() != null) {
                    continue;
                }
                final Field field = cls.getInstanceFields().get(entry.getKey());
                final AbstractVariableReference newRef =
                    ConcreteInstance.getNewFieldValue(field, curState, myRef, FieldValueSettings.GENERAL_VALUE);
                entry.setValue(newRef);
                newRefs.add(new Pair<HeapEdge, AbstractVariableReference>(new InstanceFieldEdge(current.type
                    .getClassName(), entry.getKey()), entry.getValue()));
            }
            current = current.getSuperClassInstance();
        }
        assert (!curMostSpec.hasUnrealizedField());

        return newRefs;
    }

    /**
     * Replace every occurence of the AbstractVariableReference oldRef in the
     * fields of this instance with the newRef.
     * @param oldRef the name of the variable to be replaced
     * @param newRef the new variable
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        ConcreteInstance curInstance = this.getMostSpecializedInstance();
        while (curInstance != null) {
            for (final Map.Entry<String, AbstractVariableReference> entry : curInstance.fields.entrySet()) {
                if (entry.getValue() == null) {
                    continue;
                }
                if (entry.getValue().equals(oldRef)) {
                    entry.setValue(newRef);
                }
            }
            curInstance = curInstance.superClassInstance;
        }
    }

    /**
     * @param mostSpecializedInst instance of the most specialized subclass of
     * this object
     */
    public void setMostSpecializedInstance(final ConcreteInstance mostSpecializedInst) {
        if (mostSpecializedInst == this) {
            this.mostSpecializedClass = null;
        } else {
            this.mostSpecializedClass = mostSpecializedInst;
        }
    }

    /**
     * Store a reference to the subinstance and update the pointer to the most
     * special class in every super instance.
     * @param subClassInst instance of the enclosed subclass
     */
    public void setSubClassInstance(final ConcreteInstance subClassInst) {
        this.subClassInstance = subClassInst;
        this.mostSpecializedClass = subClassInst.getMostSpecializedInstance();
        if (this.superClassInstance != null) {
            this.superClassInstance.setSubClassInstance(this);
        }
    }

    /**
     * Store a reference to the super instance.
     * @param superClassInst instance of the enclosing super class
     */
    public void setSuperClassInstance(final ConcreteInstance superClassInst) {
        this.superClassInstance = superClassInst;
    }

    /**
     * @return String representation of this {@link ConcreteInstance}.
     */
    @Override
    public String toString() {
        return this.toString(null, null, true);
    }

    /**
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param state current state
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return String representation of this {@link ConcreteInstance}.
     */
    public String toString(
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        if (this.isNULL()) {
            return "#";
        }

        final StringBuilder t = new StringBuilder();
        boolean closeBracket;
        if (state != null && (this.superClassInstance != null || this.subClassInstance == null)) {
            // don't add Object(...) every time
            t.append(this.type.getShortClassName(state.getClassPath().getClasses())).append("(");
            closeBracket = true;
        } else {
            closeBracket = false;
        }
        if (this.subClassInstance != null) {
            t.append(this.subClassInstance.toString(varUsers, state, shortRepresentation));
            if (!this.fields.isEmpty()) {
                t.append(", ");
            }
        }
        final Iterator<Entry<String, AbstractVariableReference>> fieldEntryIt = this.fields.entrySet().iterator();
        while (fieldEntryIt.hasNext()) {
            final Map.Entry<String, AbstractVariableReference> e = fieldEntryIt.next();
            if (e.getValue() == null) {
                t.append(e.getKey());
                t.append("=?");
            } else {
                t.append(e.getKey()
                    + "="
                    + PrettyVariablePrinter.prettyPrint(e.getValue(), varUsers, state, shortRepresentation));
            }

            if (fieldEntryIt.hasNext()) {
                t.append(", ");
            }
        }
        if (closeBracket) {
            t.append(")");
        }
        return t.toString();
    }

    /**
     * @return true if this instance is the NULL instance.
     */
    @Override
    public boolean isNULL() {
        return this == ConcreteInstance.NULL;
    }

    /**
     * Just set the field to the given value. Nothing more is done.
     * @param name the field name
     * @param value the new value for the field
     */
    public void setField(final String name, final AbstractVariableReference value) {
        assert (value != null);
        this.fields.put(name, value);
    }

    /**
     * @return true if this concrete instance is only realized up to jlO
     */
    public boolean isOnlyRealizedUpToJLO() {
        return this
            .getMostSpecializedInstance()
            .getType()
            .getClassName()
            .equals(Important.JAVA_LANG_OBJECT.getClassName());
    }

    /**
     * @param state the state in which this instance will live
     * @return a new ConcreteInstance representing a java.lang.Object instance
     */
    public static ConcreteInstance newJLO(final State state) {
        return ConcreteInstance.newInstanceFromType(
            state,
            state.getClassPath().getClass(Important.JAVA_LANG_OBJECT).getType(),
            FieldValueSettings.GENERAL_VALUE);
    }

    /**
     * Remove the entry for the given field
     * @param fieldName name of the field to remove
     */
    public void removeField(final String fieldName) {
        this.fields.remove(fieldName);
    }

    /**
     * Do not modify!
     * @return the names of all fields, including those for which no value is known
     */
    public Collection<String> getFieldNames() {
        return this.fields.keySet();
    }

    /**
     * @return true iff there is some field for which we stored null (so this field is not realized)
     */
    public boolean hasUnrealizedField() {
        return this.fields.values().contains(null);
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();

        res.put("Type", this.type.getClassName().toString());
        final JSONObject fields = new JSONObject();
        for (Entry<String, AbstractVariableReference> e : this.fields.entrySet()) {
            fields.put(e.getKey(), e.getValue().toString());
        }
        res.put("Fields", fields);
        if (this.subClassInstance != null) {
            res.put("Subclass Instance", this.subClassInstance.toJSON());
        }

        return res;
    }
}
