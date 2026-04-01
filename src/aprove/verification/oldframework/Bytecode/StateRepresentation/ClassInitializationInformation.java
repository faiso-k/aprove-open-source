package aprove.verification.oldframework.Bytecode.StateRepresentation;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.Bytecode.Natives.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convenience class holding information and methods related to the
 * initialization of classes in the analysis.
 *
 * @author Marc Brockschmidt
 */
public class ClassInitializationInformation implements Cloneable {
    /**
     * Collection of overwritten class initializers, made up from a bit of
     * native code and a collection of other classes to initialize.
     * First, the native code is executed, then clinit calls for all the
     * specified classes are put on the callstack (i.e., they are executed
     * in reversed order).
     */
    private static final List<Triple<ClassName, Collection<ClassName>, PredefinedMethod>> OVERWRITTEN_CLASS_INITS =
        new LinkedList<>();

    static {
        // the fields "unsafe" and "valueOffset" are never used (we overwrite the methods using them)
        OVERWRITTEN_CLASS_INITS.add(new Triple<ClassName, Collection<ClassName>, PredefinedMethod>(ClassName
            .fromDotted("java.util.concurrent.atomic.AtomicInteger"), Arrays.asList(new ClassName[] {
            //This one is just plain horrible: ClassName.fromDotted("sun.misc.Unsafe"),
            ClassName.fromDotted("sun.reflect.Reflection"),
            ClassName.fromDotted("java.util.Vector"),
            ClassName.fromDotted("java.util.Stack"),
            ClassName.fromDotted("java.util.HashMap$EntrySet"),
            ClassName.fromDotted("java.util.HashMap$EntryIterator"),
            ClassName.fromDotted("java.util.HashMap$HashIterator"),
            ClassName.fromDotted("java.util.HashMap$Entry"),
            ClassName.fromDotted("java.util.AbstractList"),
            ClassName.fromDotted("java.util.AbstractSet"),
            ClassName.fromDotted("java.util.AbstractCollection"),
            ClassName.fromDotted("java.lang.Double"),
            ClassName.fromDotted("java.lang.Math"),
            ClassName.fromDotted("java.lang.ArrayIndexOutOfBoundsException"),
            ClassName.fromDotted("java.lang.IndexOutOfBoundsException"),
            ClassName.fromDotted("java.lang.RuntimeException"),
            ClassName.fromDotted("java.lang.Exception"),
            ClassName.fromDotted("java.lang.Throwable"), }), new NativeNop(0, false)));

        // the field "unsafe" is never used
        OVERWRITTEN_CLASS_INITS.add(new Triple<ClassName, Collection<ClassName>, PredefinedMethod>(ClassName
            .fromDotted("sun.misc.SharedSecrets"), Arrays.asList(new ClassName[] {
            //This one is just plain horrible: ClassName.fromDotted("sun.misc.Unsafe"),
            ClassName.fromDotted("sun.misc.JavaUtilJarAccess"),
            ClassName.fromDotted("sun.misc.JavaLangAccess"),
            ClassName.fromDotted("sun.misc.JavaIOAccess"),
            ClassName.fromDotted("sun.misc.JavaIODeleteOnExitAccess"),
            ClassName.fromDotted("sun.misc.JavaNetAccess"),
            ClassName.fromDotted("sun.misc.JavaIOFileDescriptorAccess"), }), new NativeNop(0, false)));

        // the field "unsafe" i snever used
        OVERWRITTEN_CLASS_INITS.add(new Triple<ClassName, Collection<ClassName>, PredefinedMethod>(
            ClassName
                .fromDotted("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl"),
            Arrays.asList(new ClassName[] {
            //This one is just plain horrible: ClassName.fromDotted("sun.misc.Unsafe"),
            ClassName.fromDotted("java.util.concurrent.atomic.AtomicReferenceFieldUpdater"), }),
            new NativeNop(0, false)));
    }

    /**
     * The initialization status of some class.
     * @author cotto
     */
    public enum InitStatus {
        /**
         * We do not know.
         */
        MAYBE,

        /**
         * Not yet initialized.
         */
        NO,

        /**
         * The initializer is running.
         */
        RUNNING,

        /**
         * Initialization finished.
         */
        YES;
    }

    /**
     * Map from fully qualified classnames (e.g. java/io/Printstream to the
     * current status of initialization. YES: class is initialized, NO: class is
     * not initialized, RUNNING: the initializer is not yet done, MAYBE: we do
     * not know. The default value is defined by the strategy.
     */
    private DefaultValueMap<ClassName, InitStatus> initializedClasses;

    /**
     * Construct a new class initialization object. The default init status is
     * always MAYBE.
     */
    public ClassInitializationInformation() {
        this.initializedClasses = new DefaultValueMap<>(InitStatus.MAYBE);
    }

    /**
     * Returns a deep (!) copy of this {@link ClassInitializationInformation}
     * object.
     * @return Deep copy of this object
     */
    @Override
    public ClassInitializationInformation clone() {
        final ClassInitializationInformation clone = new ClassInitializationInformation();

        clone.initializedClasses = new DefaultValueMap<>(this.initializedClasses.getDefaultValue());
        for (final Map.Entry<ClassName, InitStatus> e : this.initializedClasses.entrySet()) {
            clone.initializedClasses.put(e.getKey(), e.getValue());
        }

        return clone;
    }

    /**
     * Ensures that all needed basic classes (i.e. what's needed for the
     * emulated JVM) are indeed initialized. If not, returns a state in which
     * the initialization process is triggered for the next missing class.
     *
     * @param s some state
     * @return a state/edge pair where some class is marked with an
     * initialization status NO (or null if this is not needed)
     */
    public Pair<State, InitializationStateChange> setBaseClassesInitState(final State s) {
        JBCOptions options = s.getJBCOptions();
        if (options.defaultClassInitState() == InitStatus.YES) {
            return null;
        }
        final ClassName[] initClasses;
        JVMBoot bootMode = s.getJBCOptions().jvmBoot();
        switch (bootMode) {
            case Competition: {
                final ClassName[] initClassesCopy =
                    {
                     JAVA_LANG_STRING.getClassName(),
                     ARRAYINDEXOOB_EXC.getClassName(),
                     s.getCurrentOpCode().getMethod().getIClass().getClassName(),
                    };
                initClasses = initClassesCopy;
                break;
            }
            case Complete: {
                /*
                 * This bootstraps the JVM "just" as the OpenJDK hotspot
                 * implementation. For the original, see create_vm from
                 * src/share/vm/runtime/thread.cpp.
                 * Summary of interesting-looking stuff in that method:
                 *  (1) do lots of stuff before creating the first ThreadLocalStorage
                 *  (2) vm_init_globals()
                 *       * checks general sanity
                 *       * initializes internal representations of primitive types
                 *  (3) new JavaThread();
                 *       * Sets all initial values to 0/NULL/false
                 *  (4) ObjectSynchronizer::Initialize()
                 *       * Initializes some counters, locks
                 *  (5) init_globals()
                 *       * Initializes most of the (boring) framework
                 *       * Links (but not initializes) "well-known classes" (list is
                 *         in src/share/classfile/systemDictionary.hpp)
                 *       * allocates permanent instances of
                 *            java_lang_OutOfMemoryError
                 *            java_lang_NullPointerException
                 *            java_lang_ArithmeticException
                 *            java_lang_VirtualMachineError
                 *            java_lang_ref_Finalizer
                 *            java_lang_NoSuchMethodException
                 *            java_lang_reflect_Method
                 *            java_lang_ClassLoader
                 *  (6) Initializes java.lang.String
                 *      Initializes java.util.HashMap
                 *      Initializes java.lang.StringValue
                 *      Initializes java.lang.System
                 *      Initializes java.lang.ThreadGroup
                 *      Initializes java.lang.ThreadGroup
                 *      Initializes java.lang.reflect.Method
                 *      Initializes java.lang.ref.Finalizer
                 *      Initializes java.lang.Class
                 *      Initializes java.lang.OutOfMemoryError
                 *      Initializes java.lang.NullPointerException
                 *      Initializes java.lang.ClassCastException
                 *      Initializes java.lang.ArrayStoreException
                 *      Initializes java.lang.ArithmeticException
                 *      Initializes java.lang.StackOverflowError
                 *      Initializes java.lang.IllegalMonitorStateException
                 *      Initializes java.lang.Compiler
                 */
                final ClassName[] initClassesCopy =
                    {
                     JAVA_LANG_STRING.getClassName(),
                     JAVA_LANG_SYSTEM.getClassName(),
                     JAVA_LANG_THREADGROUP.getClassName(),
                     JAVA_LANG_THREAD.getClassName(),
                     JAVA_LANG_CLASS.getClassName(),
                     /*
                      * Note:
                      * In the implementation for the return opcode, it is
                      * hardcoded that System.initializeSystemClass() is called
                      * when the initializer of java.lang.System completes. This
                      * corresponds to the behaviour implemented in OpenJDK.
                      */
                     NPE_EXC.getClassName(),
                     CLASSCAST_EXC.getClassName(),
                     ARRAYSTORE_EXC.getClassName(),
                     ARITH_EXC.getClassName(),
                     ARRAYINDEXOOB_EXC.getClassName(),
                     NOCLASSDEFFOUND_ERR.getClassName(),
                     ILLEGALACCESS_ERR.getClassName(),
                     INCOMPATIBLECLASSCHANGE_ERR.getClassName(),
                     ABSTRACTMETHOD_ERR.getClassName(),
                     s.getCurrentOpCode().getMethod().getIClass().getClassName(),
                    };
                initClasses = initClassesCopy;
                break;
            }
            case None: {
                initClasses = new ClassName[0];
                break;
            }
            default: {
                throw new RuntimeException("Unknown JVMBoot mode " + bootMode);
            }
        }

        /*
         * Initialize the collected classes one by one. This also means to
         * return if some class is not yet initialized or the initializer is
         * still running, instead of starting the initialization process for
         * another class.
         */
        for (final ClassName className : initClasses) {
            final InitStatus currentStatus = this.initializedClasses.get(className);
            if (currentStatus == InitStatus.MAYBE) {
                final State clone = s.clone();
                final ClassInitializationInformation clonedInitInfo = clone.getClassInitInfo();

                final Collection<Triple<ClassName, InitStatus, InitStatus>> newStates = new LinkedHashSet<>();
                clonedInitInfo.setInitialized(className, InitStatus.NO);
                newStates.add(new Triple<>(className, InitStatus.NO, InitStatus.MAYBE));

                // also initialize the super types
                TypeTree tree = clone.getClassPath().getTypeTree(className).getSuperType();
                while (tree != null) {
                    final InitStatus superStatus = clonedInitInfo.getInitializationState(tree.getClassName(), options);
                    if (superStatus == InitStatus.MAYBE) {
                        clonedInitInfo.setInitialized(tree.getClassName(), InitStatus.NO);
                        newStates.add(new Triple<>(tree.getClassName(), InitStatus.NO, InitStatus.MAYBE));
                    }
                    tree = tree.getSuperType();
                }
                return new Pair<>(clone, new InitializationStateChange(newStates));
            } else if (currentStatus == InitStatus.RUNNING || currentStatus == InitStatus.NO) {
                return null;
            }
        }
        return null;
    }

    /**
     * Initializes all classes that are marked with InitStatus.NO (which means
     * that they are not initialized yet, but we want them to be initialized).
     * We do this by creating a new state in which the class initializer of
     * such a class is executed (e.g. by adding a stackframe for the
     * corresponding &lt;clinit&gt; method).
     *
     * @param s some state
     * @return a state/edge pair where some class marked with an
     * initialization status NO was changed to RUNNING/YES and the corresponding
     * state changes were performed. Returns null if that's not needed.
     */
    public Pair<State, InitializationStateChange> initializeNeededClasses(final State s) {
        if (s.getJBCOptions().defaultClassInitState() == InitStatus.YES) {
            assert Collections.singleton(InitStatus.YES).containsAll(initializedClasses.values());
            return null;
        }
        final ClassPath cPath = s.getClassPath();
        final Collection<TypeTree> candidates = new LinkedHashSet<>();
        for (final Map.Entry<ClassName, InitStatus> entry : this.initializedClasses.entrySet()) {
            final InitStatus ynm = entry.getValue();
            if (ynm == InitStatus.NO) {
                final TypeTree tree = cPath.getTypeTree(entry.getKey());
                candidates.add(tree);
            }
        }

        if (candidates.isEmpty()) {
            return null;
        }

        /*
         * We need to start with the single "most sub" class which is not
         * initialized.
         */
        OUTER: while (candidates.size() > 1) {
            final TypeTree candidate = candidates.iterator().next();
            final ClassName className = candidate.getClassName();
            for (final TypeTree other : candidates) {
                if (other.isProperSubClassOf(className)) {
                    candidates.remove(candidate);
                    continue OUTER;
                }
                if (candidate.isProperSubClassOf(other.getClassName())) {
                    candidates.remove(other);
                    continue OUTER;
                }
            }
            assert (false);
        }

        final TypeTree candidate = candidates.iterator().next();
        final IClass parsedClass = cPath.getClass(candidate.getClassName());
        final Pair<State, Collection<Triple<ClassName, InitStatus, InitStatus>>> p = initializeAfterAllParents(s, parsedClass);
        final State clone = p.x;
        assert (clone != null);
        return new Pair<>(clone, new InitializationStateChange(p.y));
    }

    /**
     * We expect the class to not have been initialized yet. If this is the
     * case, this modifies the state as follows: All fields of all parents of
     * the class specified by the classname and the fields of the class itself
     * are brought to existence, and are filled with the most general values.
     * Furthermore, if the class has a &lt;clinit&gt; method, that method is pushed
     * onto the stack.
     * @param state the state in which the call to &lt;clinit&gt; should be done.
     * @param parsedClass The class to initialize
     * @return the modified state in which initialization has begun
     */
    public static State callClinit(final State state, final IClass parsedClass) {
        assert state.getJBCOptions().defaultClassInitState() != InitStatus.YES;
        State clone = state.clone();
        if (ObjectRefinement.hasNoopInit(parsedClass, clone.getClassInitInfo().initializedClasses)) {
            clone.getClassInitInfo().setInitialized(parsedClass.getClassName(), InitStatus.YES);
            return clone;
        }
        final ClassName cName = parsedClass.getClassName();
        final InitStatus wasInitialized = clone.getClassInitInfo().getInitializationState(cName, state.getJBCOptions());
        assert (wasInitialized == InitStatus.NO);

        VariableInitialization.fillStaticFieldsWithDefaultValues(clone, parsedClass);
        VariableInitialization.fillStaticFieldsWithConstantValues(clone, parsedClass);

        //Try to check if this class initializer was overwritten natively:
        for (final Triple<ClassName, Collection<ClassName>, PredefinedMethod> t : OVERWRITTEN_CLASS_INITS) {
            final ClassName cn = t.x;
            if (cName.equals(cn)) {
                final PredefinedMethod methImpl = t.z;
                clone.getClassInitInfo().setInitialized(cName, InitStatus.YES);

                final Collection<ClassName> otherClassesToInit = t.y;
                clone = methImpl.evaluate(clone).x;

                //Set init status to NO for all classes we want to start the initializer for:
                final ClassInitializationInformation cloneInitInfo = clone.getClassInitInfo();
                for (final ClassName cnToInit : otherClassesToInit) {
                    if (cloneInitInfo.getInitializationState(cnToInit, state.getJBCOptions()) != InitStatus.YES
                        && cloneInitInfo.getInitializationState(cnToInit, state.getJBCOptions()) != InitStatus.RUNNING)
                    {
                        cloneInitInfo.setInitialized(cnToInit, InitStatus.NO);
                    }
                }

                for (final ClassName cnToInit : otherClassesToInit) {
                    if (cloneInitInfo.getInitializationState(cnToInit, state.getJBCOptions()) != InitStatus.YES
                        && cloneInitInfo.getInitializationState(cnToInit, state.getJBCOptions()) != InitStatus.RUNNING)
                    {
                        final Pair<State, Collection<Triple<ClassName, InitStatus, InitStatus>>> p =
                            initializeAfterAllParents(clone, clone.getClassPath().getClass(cnToInit));
                        clone = p.x;
                    }
                }

                return clone;
            }
        }

        IMethod clInitMethod = null;
        for (final IMethod method : parsedClass.getMethods()) {
            if (method.isClassInitializer()) {
                clInitMethod = method;
            }
        }
        if (clInitMethod == null) {
            clone.getClassInitInfo().setInitialized(cName, InitStatus.YES);
        } else {
            clone.getClassInitInfo().setInitialized(cName, InitStatus.RUNNING);
            clone.getCallStack().push(new StackFrame(clInitMethod));
        }

        return clone;
    }

    /**
     * @param state the state in which we need to do some initialization
     * @param classToInit Class to check initialization for
     * @return the new state in which initialization has begun and the number
     *  of added initializer stackframes.
     */
    private static Pair<State, Collection<Triple<ClassName, InitStatus, InitStatus>>> initializeAfterAllParents(
        final State state,
        final IClass classToInit)
    {
        final ClassInitializationInformation curInitInfo = state.getClassInitInfo();
        final LinkedHashSet<Triple<ClassName, InitStatus, InitStatus>> newInitStates = new LinkedHashSet<>();
        final InitStatus curInitStatus = curInitInfo.getInitializationState(classToInit.getClassName(), state.getJBCOptions());
        switch (curInitStatus) {
        case MAYBE:
            assert (false) : "This method should never be called with MAYBE as initialization status";
            return null;
        case YES:
        case RUNNING:
            // Nope, nothing to be done
            return new Pair<State, Collection<Triple<ClassName, InitStatus, InitStatus>>>(state.clone(), newInitStates);
        case NO:
            // OK, the requested class has not been initialized yet.
            IClass pcp = classToInit;
            State curState = state;
            parentLoop: while (true) {
                switch (curInitInfo.getInitializationState(pcp.getClassName(), state.getJBCOptions())) {
                case YES:
                case RUNNING:
                    break parentLoop;
                case NO:
                    curState = callClinit(curState, pcp);
                    final ClassName initedClass = pcp.getClassName();
                    newInitStates.add(new Triple<>(initedClass, curState.getClassInitInfo().getInitializationState(
                        initedClass, state.getJBCOptions()), InitStatus.NO));
                    break;
                case MAYBE:
                    assert (false) : "We should not find a class initialization state MAYBE "
                        + "above an initialization state NO";
                    break;
                default:
                    assert (false);
                }
                final TypeTree superType = pcp.getType().getSuperType();
                if (superType == null) {
                    break;
                }
                pcp = state.getClassPath().getClass(superType.getClassName());
            }
            return new Pair<State, Collection<Triple<ClassName, InitStatus, InitStatus>>>(curState, newInitStates);
        default:
            throw new RuntimeException("Case fallthrough");
        }
    }

    /**
     * <b>Do not modify return value</b>
     * @return The set of classes which are have initialization state YES, NO,
     * RUNNING or MAYBE (i.e. not null)
     */
    public Map<ClassName, InitStatus> getClassesWithInitializationState(JBCOptions options) {
        if (options.defaultClassInitState() == InitStatus.YES) {
            assert Collections.singleton(InitStatus.YES).containsAll(initializedClasses.values());
        }
        return this.initializedClasses;
    }

    /**
     * Store the initialization status for the given class.
     * @param className some class
     * @param value the new initialization status
     */
    public void setInitialized(
        final ClassName className,
        final InitStatus value)
    {
        if (Globals.useAssertions) {
            assert (value != null) : "null is not allowed";
        }
        final InitStatus old = this.initializedClasses.put(className, value);
        assert (old != InitStatus.YES || value == old);
    }

    /**
     * Mark the given class and all its superclasses as having been initialized,
     * and set their static fields to the most general value
     * @param state to work on
     * @param pc bottommost class
     * @return the set of changed classes with their new init status
     */
    public Collection<Triple<ClassName, InitStatus, InitStatus>> setInitializedRecursively(final State state, final IClass pc) {
        assert state.getJBCOptions().defaultClassInitState() != InitStatus.YES;
        final Collection<Triple<ClassName, InitStatus, InitStatus>> newInitStates = new LinkedHashSet<>();
        final ClassName cn = pc.getClassName();
        final InitStatus oldState = this.getInitializationState(cn, state.getJBCOptions());
        if (oldState == InitStatus.YES || oldState == InitStatus.RUNNING)
        {
            return newInitStates;
        }
        VariableInitialization.fillStaticFieldsWithGeneralValues(state, pc);
        this.setInitialized(cn, InitStatus.YES);
        newInitStates.add(new Triple<>(cn, InitStatus.YES, oldState));

        final TypeTree superType = pc.getSuperType();
        if (superType != null) {
            final IClass superClass = state.getClassPath().getClass(superType.getClassName());
            newInitStates.addAll(this.setInitializedRecursively(state, superClass));
        }
        return newInitStates;
    }

    /**
     * @param cn some class
     * @return the initialization status for the given class (never null)
     */
    public InitStatus getInitializationState(final ClassName cn, JBCOptions options) {
        if (options.defaultClassInitState() == InitStatus.YES) {
            assert Collections.singleton(InitStatus.YES).containsAll(initializedClasses.values());
            return InitStatus.YES;
        }
        assert (this.initializedClasses.getDefaultValue() != null);
        return this.initializedClasses.get(cn);
    }

    /**
     * @param sb a Stringbuilder into which the output is written
     * @param classPath the enclosing JBC program
     */
    public void toString(final StringBuilder sb, final ClassPath classPath, JBCOptions options) {
        final Collection<ClassName> classes = classPath.getClasses();
        final CollectionMap<InitStatus, ClassName> map = new CollectionMap<>();
        for (final Map.Entry<ClassName, InitStatus> entry : this.getClassesWithInitializationState(options).entrySet()) {
            map.add(entry.getValue(), entry.getKey());
        }
        int javaLangInit = 0;
        for (final InitStatus status : InitStatus.values()) {
            if (map.containsKey(status)) {
                sb.append(status);
                sb.append(": ");
                int length = 0;
                final Iterator<ClassName> it = map.get(status).iterator();
                while (it.hasNext()) {
                    final ClassName className = it.next();
                    if (status == InitStatus.YES && "java/lang".equals(className.getPkgName())) {
                        javaLangInit++;
                        continue;
                    }
                    final TypeTree tree = classPath.getTypeTree(className);
                    final String shortName = tree.getShortClassName(classes);
                    sb.append(shortName);
                    length += shortName.length();
                    if (it.hasNext()) {
                        if (length >= 100) {
                            sb.append(",\n");
                            length = 0;
                        } else {
                            sb.append(", ");
                        }
                    }
                }
                if (javaLangInit > 0) {
                    sb.append(" (JL");
                    sb.append(javaLangInit);
                    sb.append(")");
                }
                sb.append("\n");
            }
        }
    }
}
