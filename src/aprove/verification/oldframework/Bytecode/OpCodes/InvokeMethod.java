/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;
import static java.lang.invoke.MethodHandleInfo.*;
import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Natives.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of method and constructor invocation opcodes.
 */
public class InvokeMethod extends OpCode {

    public static final Logger logger = Logger.getLogger(InvokeMethod.class.getName());

    /**
     * Enumeration of possible invocation types.
     */
    public enum InvocationType {
        /**
         * Instance method invocation.
         */
        VIRTUAL,
        /**
         * Constructor, superclass or private method invocation.
         */
        SPECIAL,
        /**
         * Static method invocation.
         */
        STATIC,
        /**
         * Interface method invocation.
         */
        INTERFACE,
        /**
         * Dynamic!
         */
        DYNAMIC,
        /**
         * newInvokeSpecial -- used to pass references to constructors; results in generating the bytecode
         * new C
         * dup
         * involespecial C.<init>
         * at runtime
         */
        NEWSPECIAL;

        public static InvocationType fromInt(int i) {
            switch (i) {
                case REF_invokeInterface:
                    return INTERFACE;
                case REF_invokeStatic:
                    return STATIC;
                case REF_invokeVirtual:
                    return VIRTUAL;
                case REF_invokeSpecial:
                    return SPECIAL;
                case REF_newInvokeSpecial:
                    return NEWSPECIAL;
                default:
                    throw new IllegalArgumentException();
            }
        }
    }

    /**
     * Type of invocation represented by this instance.
     */
    private final InvocationType invocationType;

    /**
     * Identifier of the method to be invoked.
     */
    private final MethodIdentifier methodIdentifier;

    /**
     * If true, after this method invocation, the result of that invocation is
     * returned without any further side-effects or possible non-termination.
     * Because of exceptions and complicated "no-ops" this only is an
     * approximation.
     */
    private Boolean tailCall;

    /**
     * The resolved method.
     */
    private volatile IMethod resolvedMethod;

    /**
     * @param invType Kind of invocation (Virtual, Static, etc...)
     * @param methodId Identifier of the method to be invoked.
     */
    public InvokeMethod(final InvocationType invType, final MethodIdentifier methodId) {
        this.invocationType = invType;
        this.methodIdentifier = methodId;
    }

    /**
     * @return String representation of this {@link InvokeMethod} opcode.
     */
    @Override
    public String toString() {
        return this.toString(false);
    }

    /** {@inheritDoc} */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
            if (this.invocationType == InvocationType.DYNAMIC) {
                throw new RuntimeException();
            }

            //Resolve method according to §5.4.3.(3|4) (JVMS 3rd edition).
            this.resolveMethod();

            if (this.resolvedMethod == null) {
                final Important[] refineNeeded =
                    {
                     Important.NOCLASSDEFFOUND_ERR,
                     Important.ILLEGALACCESS_ERR,
                     Important.INCOMPATIBLECLASSCHANGE_ERR,
                     Important.NOSUCHMETHOD_ERR,
                     Important.ABSTRACTMETHOD_ERR,
                     Important.ILLEGALACCESS_ERR, };
                for (final Important err : refineNeeded) {
                    if (ObjectRefinement.forInitialization(err, s, out)) {
                        return true;
                    }
                }
                return false;
            }

            TerminationGraph termG = s.getTerminationGraph();
            boolean overwritten = termG.getPredefinedMethods().isOverriden(resolvedMethod, s);

            if (this.invocationType != InvocationType.STATIC) {
                /*
                 * First ensure that non-static calls have an actual object instance
                 * on the stack:
                 */
                final AbstractVariableReference objectRef =
                        s
                        .getCurrentStackFrame()
                        .getOperandStack()
                        .peek(this.methodIdentifier.getDescriptor().getArgumentCount());
                if (ObjectRefinement.forExistence(objectRef, s, out)) {
                    return true;
                }
                if (objectRef.isNULLRef()) {
                    return ObjectRefinement.forInitialization(Important.NPE_EXC, s, out);
                }

                if (!overwritten) {
                    /*
                     * Now find out which classes provide implementations for the
                     * resolved method. For invokespecial, the executed implementation
                     * of the method is selected based on the fixed data in the class
                     * file (as argument to the opcode) and thus needs no further
                     * refinement.
                     */
                    if (this.invocationType == InvocationType.INTERFACE || this.invocationType == InvocationType.VIRTUAL) {
                        final List<FuzzyType> classes = new LinkedList<>();
                        final AbstractType baseType = s.getAbstractType(objectRef);
                        final ClassPath cPath = s.getClassPath();
                        final Collection<ClassName> implementingClasses =
                                getClassesImplementingMethod(
                                        baseType,
                                        this.resolvedMethod,
                                        this.methodIdentifier,
                                        this.invocationType == InvocationType.VIRTUAL,
                                        cPath);

                        if (this.invocationType == InvocationType.INTERFACE) {
                            /*
                             * For the types that implement the target method without
                             * implementing the interface of the target method we need
                             * to throw an error.
                             */
                            final ClassName declaringInterface = this.resolvedMethod.getClassName();
                            for (final ClassName className : implementingClasses) {
                                final TypeTree type = cPath.getTypeTree(className);
                                if (!declaringInterface.equals(JAVA_LANG_OBJECT.getClassName())
                                        && !type.implementsInterface(declaringInterface))
                                {
                                    assert (false) : "invokeinterface: "
                                            + className.toString()
                                            + " needs to implement "
                                            + declaringInterface.toString();
                                    // TODO we'd need to throw an IncompatibleClassChangeError here
                                } else if (!RawMethod.isPublic(type.getMethodAccessFlags(this.methodIdentifier).intValue())) {
                                    assert (false);
                                    // TODO we'd need to throw an IllegalAccessError here
                                } else {
                                    classes.add(new FuzzyClassType(className, true));
                                }
                            }
                        } else {
                            for (final ClassName className : implementingClasses) {
                                classes.add(new FuzzyClassType(className, true));
                            }
                        }

                        if (!classes.isEmpty()) {
                            if (ObjectRefinement.forTypesOfInterest(objectRef, classes, true, s, out)) {
                                if (out.isEmpty()) {
                                    logger.severe("missing implementation: trying to evaluate " + methodIdentifier + ", but there is no implementing class");
                                    if (s.getJBCOptions().summarizeOnMissingImplementations()) {
                                        s.getTerminationGraph().getPredefinedMethods().forceOverwriteWithDefaultSummary(resolvedMethod, s.getTerminationGraph().getGoal(), "no implementation");
                                        return false;
                                    }
                                    if (!s.getJBCOptions().continueOnMissingImplementations()) {
                                        throw new RuntimeException("No implementation for " + methodIdentifier + " in the classpath");
                                    }
                                }
                                return true;
                            }
                        }
                    }
                }
            }

            // TODO: edge cases, correct location?
            PredefinedMethodHolder predef = s.getTerminationGraph().getPredefinedMethods();
            if (predef.hasOverridingMethod(resolvedMethod, s)) {
                PredefinedMethod predefinedMethod = predef.getOverwritingMethod(resolvedMethod, s);
                if (predefinedMethod.isApplicable(s)) {
                    return predefinedMethod.refine(s, out);
                }
            }

            if (!overwritten) {
                /*
                 * We were able to resolve the method, now get the actual
                 * implementation to evaluate:
                 */
                final IMethod target = this.getTargetMethod(s, s.getClassPath());
                if (target != null) {
                    if (target.isAbstract()) {
                        return ObjectRefinement.forInitialization(ABSTRACTMETHOD_ERR, s, out);
                    }
                    // Now check if the class we're interested in has already been loaded
                    if (ObjectRefinement.forInitialization(s.getClassPath().getClass(target.getClassName()), s, out)) {
                        return true;
                    }

                    if (target.isNative()) {
                        PredefinedMethod nat = getNativeMethod(target, s.getTerminationGraph().getPredefinedMethods());
                        if (nat == null) {
                            return handleMissingNativeMethod(s, out, target);
                        } else {
                            return nat.refine(s, out);
                        }
                    }
                } else {
                    /*
                     * If the method couldn't be resolved, we need to initialize the
                     * corresponding error.
                     */
                    if (ObjectRefinement.forInitialization(ClassName.Important.ABSTRACTMETHOD_ERR, s, out)) {
                        return true;
                    }
                }
            }

            return false;
    }

    private boolean handleMissingNativeMethod(State s, Collection<Pair<State, ? extends EdgeInformation>> out, IMethod target) {
        if (s.getJBCOptions().summarizeUnimplementedNativeMethods()) {
            s.getTerminationGraph().getPredefinedMethods().forceOverwriteWithDefaultSummary(target, s.getTerminationGraph().getGoal(), "unimplemented native method");
            return refine(s, out);
        } else {
            throw new NotYetImplementedException("Native method "
                    + target
                    + " in class "
                    + target.getClassName()
                    + " not yet "
                    + "implemented for call in this state:\n"
                    + s);
        }
    }

    /** {@inheritDoc} */
    @Override
    public final Pair<State, ? extends EdgeInformation> evaluate(final State s) {
        if (this.invocationType == InvocationType.DYNAMIC) {
            throw new RuntimeException();
        }
        final State newState = s.clone();

        final boolean isTailCall = this.isTailCall(s.getJBCOptions());

        //Resolve method according to §5.4.3.3 (JVMS 3rd edition).
        if (this.resolvedMethod == null) {
            Resolver.resolveMethodOrThrow(s.getClassPath(), this.methodIdentifier, newState, this
                .getMethod()
                .getIClass()
                .getType(), this.invocationType == InvocationType.INTERFACE);
            /*
             * In this case the resolveMethodOrThrow has already thrown an
             * error in newState.
             */
            return new Pair<>(newState, new MethodStartEdge());
        }

        /*
         * First ensure that non-static calls have an actual object instance on
         * the stack:
         */
        final boolean isStatic = this.invocationType == InvocationType.STATIC;
        if (!isStatic) {
            final AbstractVariableReference objectRef =
                s
                    .getCurrentStackFrame()
                    .getOperandStack()
                    .peek(this.methodIdentifier.getDescriptor().getArgumentCount());

            if (objectRef.isNULLRef()) {
                OpCode.throwException(newState, NPE_EXC);
                return new Pair<>(newState, new MethodStartEdge());
            }
        }

        //Check if resolved method is overwritten
        PredefinedMethodHolder predef = s.getTerminationGraph().getPredefinedMethods();
        if (predef.hasOverridingMethod(resolvedMethod, s)) {
            PredefinedMethod predefinedMethod = predef.getOverwritingMethod(resolvedMethod, s);
            if (predefinedMethod.isApplicable(s)) {
                return predefinedMethod.evaluate(s);
            }
        }

        //Get the actual target method:
        final IMethod target = this.getTargetMethod(newState, newState.getClassPath());

        //Now evaluate it, or throw an error if we aren't able to do so:
        if (target == null) {
            assert (!isStatic) : "Undefined behavior in this case";
            OpCode.throwException(newState, ABSTRACTMETHOD_ERR);
            return new Pair<>(newState, new MethodStartEdge());
        }

        //Check if target method is overwritten
        if (predef.hasOverridingMethod(target, s)) {
            PredefinedMethod predefinedMethod = predef.getOverwritingMethod(target, s);
            if (predefinedMethod.isApplicable(s)) {
                return predefinedMethod.evaluate(s);
            }
        }

        if (target.isAbstract()) {
            OpCode.throwException(newState, ABSTRACTMETHOD_ERR);
            return new Pair<>(newState, new MethodStartEdge());
        }
        if (target.isNative()) {
            final PredefinedMethod nat = getNativeMethod(target, s.getTerminationGraph().getPredefinedMethods());
            if (nat == null) {
                throw new NotYetImplementedException("Native method "
                    + target
                    + " in class "
                    + target.getClassName()
                    + " not yet "
                    + "implemented for call in this state:\n"
                    + s);
            }
            return nat.evaluate(s);
        } else if (target.getClassName().equals(JAVA_LANG_OBJECT.getClassName())
            && target.isInstanceInitializer()
            && target.getDescriptor().getArgumentCount() == 0)
        {
            return new NativeNop(1).evaluate(s);
        }

        //setup the new stack
        addNewStackFrame(newState, target, isStatic, isTailCall);

        if (!isTailCall) {
            final OperandStack opStack = newState.getCallStack().get(1).getOperandStack();
            // remove the arguments of the method invocation
            for (int i = 0; i < target.getMethodIdentifier().getDescriptor().getArgumentCount(); i++) {
                opStack.pop();
            }

            //Also pop the ref to this for non-static invocations:
            if (this.invocationType != InvocationType.STATIC) {
                opStack.pop();
            }
        }

        return new Pair<>(newState, new MethodStartEdge(isTailCall));
    }

    /**
     * @param baseType the {@link AbstractType} describing all classes to be
     * considered.
     * @param resolvedMethod the result of the method resolution process.
     * @param methodIdentifier the method identifier (symbolic reference to
     * class and package name set by the compiler, method name and method
     * signature).
     * @param getOverridingMethods switch indicating whether methods overriding
     * <code>methodIdentifier</code> (c.f. JVMS 3rd §5.4.2.1) or methods with
     * the same name/descriptor should be returned.
     * @param cPath The considered class path for this analysis.
     * @return for all classes represented by baseType, return the most special
     * ("far away from object") class containing an overriding implementation of
     * the resolved method (or containing methods with the same name, depending
     * on the getOverridingMethods argument). This may be empty!
     */
    private static Collection<ClassName> getClassesImplementingMethod(
        final AbstractType baseType,
        final IMethod resolvedMethod,
        final MethodIdentifier methodIdentifier,
        final boolean getOverridingMethods,
        final ClassPath cPath)
    {
        final Collection<ClassName> result = new LinkedHashSet<>();
        final TypeTree methodType = cPath.getTypeTree(methodIdentifier.getClassName());

        /*
         * Prepare to work on the complete expansion of the abstract type
         * baseType, and all of the superclasses. That way, we correctly
         * handle inherited method implementations. Consider the following
         * type tree (types are numbered, types that implement something that
         * looks like methodIdentifier are marked with +)
         *
         *                      jlO
         *         .-------------'----------.
         *        0+                         2
         *        |                          |
         *        1+                         |
         *        |                          |
         *        3                          4
         *       /|\                        / \
         *      / | \                      /   \
         *     /  |  \                    /     \
         *    5+  6   7                  8       9+
         *
         * Consider the abstract type {3..., 4...}. The final type refinement
         * should look like {{5}, {3,6,7}, {4,8}, {9}}. To get that, we need
         * to check whether 1 and 2 "implement the method".
         * If we don't consider superclasses, {3,6,7,4,8} would be handled
         * alike, even as the first three could actually invoke the
         * implementation in 1.
         *
         * We do not need to return 0, because it is irrelevant for 4... and for
         * 3... is overridden by 1.
         */

        final LinkedList<FuzzyType> todo = new LinkedList<>();
        todo.addAll(baseType.getPossibleClassesCopy());
        while (!todo.isEmpty()) {
            final FuzzyType fuzzyType = todo.pop();
            if (fuzzyType.isArrayType()) {
                todo.add(FuzzyClassType.FT_JAVA_LANG_OBJECT);
                continue;
            }
            assert (fuzzyType instanceof FuzzyClassType);
            final FuzzyClassType fuzzyClass = (FuzzyClassType) fuzzyType;

            final ClassName minClass = fuzzyClass.getMinimalClass();
            final TypeTree typeTree = cPath.getTypeTree(minClass);
            if (!typeTree.isSubClassOf(methodType) && !typeTree.implementsInterface(methodType)) {
                continue;
            }

            final Integer methodAccessFlags = typeTree.getMethodAccessFlags(methodIdentifier);
            boolean found = false;
            if (methodAccessFlags != null) {
                final int flags = methodAccessFlags.intValue();
                // there is a method with the same name and descriptor
                if (RawMethod.isAbstract(flags)) {
                    found = false;
                } else if (getOverridingMethods) {
                    // see JVMS 3rd edition 5.4.2.1, also see ParsedClass.getMethod
                    if (!RawMethod.isPrivate(flags)
                        && typeTree.isSubClassOf(methodType)
                        && (RawMethod.isPublic(flags) || RawMethod.isProtected(flags) || resolvedMethod
                            .getClassName()
                            .getPkgName()
                            .equals(typeTree.getClassName().getPkgName())))
                    {
                        found = true;
                    }
                } else {
                    found = true;
                }
            }
            if (found) {
                result.add(minClass);
            } else {
                final TypeTree superType = typeTree.getSuperType();
                if (superType != null) {
                    final FuzzyClassType fuzzySuper = new FuzzyClassType(superType.getClassName(), true);
                    todo.add(fuzzySuper);
                }
            }

            if (!fuzzyClass.isConcrete()) {
                for (final TypeTree subType : typeTree.getSubTypes()) {
                    final FuzzyClassType fuzzySub = new FuzzyClassType(subType.getClassName(), false);
                    todo.add(fuzzySub);
                }
                for (final TypeTree implementor : typeTree.getImplementingTypes()) {
                    final FuzzyClassType fuzzySub = new FuzzyClassType(implementor.getClassName(), false);
                    todo.add(fuzzySub);
                }
            }
        }

        return result;
    }

    /**
     * Creates a new stack frame for a method call and moves arguments from the
     * operand stack in state to the local variable in the new stack frame. If
     * the method call is non-static, an instance reference is also provided for
     * the new stack frame.
     * @param state will be modified to the new state
     * @param newMethod instance representing the method to invoke
     * @param isStatic marks if this is a static invocation
     * @param isTailCall if true, we do not need to retain the current stack
     * frame
     * @return the new stack frame
     */
    public static StackFrame addNewStackFrame(
        final State state,
        final IMethod newMethod,
        final boolean isStatic,
        final boolean isTailCall)
    {
        assert (!newMethod.isAbstract());
        assert (!newMethod.isNative());
        final StackFrame newFrame = new StackFrame(newMethod);

        // copy arguments from stack to local variable array
        final OperandStack opStack = state.getCurrentStackFrame().getOperandStack();
        newFrame.initLocalVariables(opStack);

        if (isTailCall) {
            state.getCallStack().pop();
        }
        state.addFrame(newFrame);
        return newFrame;
    }

    /**
     * Delete the arguments from the operand stack and advance the opcode. This
     * is called from the return statements of the method invoked by this
     * opcode.
     * @param newState the state that should be cleaned.
     */
    public void handleReturn(final State newState) {
        final StackFrame sf = newState.getCurrentStackFrame();
        /*
         * If the virtual machine needs to create an exception (e.g. due to a
         * NPE), the constructor of the exception is executed by just adding the
         * corresponding stack frame. After returning from this constructor, the
         * underlying opcode is not the corresponding invokemethod opcode, but
         * instead some opcode that caused the exception to be thrown.
         * Therefore, in this situation, evaluation continues by handling the
         * (now initialized) exception and not with the following opcode.
         */
        if (!sf.hasException()) {
            sf.setCurrentOpCode(this.getNextOp());
        }
    }

    /**
     * @param detail if false, className and descriptor are omitted in the
     * output
     * @return a wonderful string representation
     */
    @Override
    public String toString(final boolean detail) {
        if (detail) {
            return this.methodIdentifier.toString();
        }
        return this.methodIdentifier.getClassName() + "." + this.methodIdentifier.getMethodName();
    }

    /**
     * @param state the state based on which we are searching for a method (may
     * be null for static, special)
     * @param classPath the class path
     * @return The method to be evaluated, as defined for the current opcode.
     */
    public IMethod getTargetMethod(final State state, final ClassPath classPath) {
        final IMethod targetMethod;
        switch (this.invocationType) {
        case STATIC:
            targetMethod = this.resolvedMethod;
            break;
        case SPECIAL:
            /* Now, proceed with invocation unless the following three conditions
             * are true:
             * (1) The ACC_SUPER flag is set for the current class.
             * (2) The class of the resolved method is a superclass of the
             *     current class.
             * (3) The resolved method is not an instance initialization method.
             *     (See JVMS 3.9:
             *       "instance initialization method [...] has the special name <init>")
             */
            final IClass thisClass = this.getMethod().getIClass();
            final IClass resolvedClass = this.resolvedMethod.getIClass();
            if (thisClass.getType().hasSuperFlag()
                && thisClass.getType().isProperSubClassOf(resolvedClass.getClassName())
                && !this.resolvedMethod.isInstanceInitializer())
            {
                final IClass superClass = classPath.getClass(thisClass.getSuperType().getClassName());
                targetMethod = superClass.getMethodRecursively(this.resolvedMethod.getMethodIdentifier());
            } else {
                targetMethod = this.resolvedMethod;
            }
            break;
        case VIRTUAL:
        case INTERFACE:
            if (this.resolvedMethod.isSignaturePolymorphic()) {
                throw new NotYetImplementedException();
            }
            final AbstractVariableReference objectRef =
                state
                    .getCurrentStackFrame()
                    .getOperandStack()
                    .peek(this.resolvedMethod.getDescriptor().getArgumentCount());

            TerminationGraph termG = state.getTerminationGraph();
            AbstractType t = state.getAbstractType(objectRef);
            Set<FuzzyType> types = null;
            if (termG.getJBCOptions().dontExpandTypeTree() && t.isAbstractJLOLike()) {
                termG.getPredefinedMethods().forceOverwriteWithDefaultSummary(resolvedMethod, termG.getGoal(), "must not expand type tree");
                return null;
            }
            types = t.expand(classPath, state.getJBCOptions());
            if (state.getJBCOptions().summarizeOnMissingImplementations() && types.isEmpty()) {
                logger.severe("missing implementation: no implmentation for " + resolvedMethod.getMethodIdentifier());
                termG.getPredefinedMethods().forceOverwriteWithDefaultSummary(resolvedMethod, termG.getGoal(), "missing implementation");
                return null;
            }
            // only consider non-abstract classes
            final AbstractType objectType =
                new AbstractType(classPath, state.getJBCOptions(), types);
            IMethod target = null;
            /*
             * The abstract type may offer several alternatives, but the method
             * to run must be clear at this point (after refinement).
             */
            Boolean implemented = null;
            for (final FuzzyType fuzzyType : objectType.getPossibleClassesCopy()) {
                if (fuzzyType instanceof FuzzyClassType) {
                    final FuzzyClassType fuzzyClassType = (FuzzyClassType) fuzzyType;
                    final ClassName minType;
                    if (fuzzyClassType.isArrayType()) {
                        minType = ClassName.Important.JAVA_LANG_OBJECT.getClassName();
                    } else {
                        minType = fuzzyClassType.getMinimalClass();
                    }
                    final IClass parsedClass = classPath.getClass(minType);

                    MethodIdentifier mid = this.resolvedMethod.getMethodIdentifier();
                    IMethod candidate = parsedClass.getOverridingMethod(mid);
                    if (candidate == null) {
                        Set<IMethod> candidates = parsedClass.getType().getImplementedInterfaces().stream().
                                map(x -> classPath.getClass(x.getClassName()).getOverridingMethod(mid)).
                                collect(toSet());
                        assert candidates.size() == 1;
                        candidate = candidates.iterator().next();
                    }
                    if (this.invocationType == InvocationType.INTERFACE
                        && !this.resolvedMethod.getClassName().equals(JAVA_LANG_OBJECT.getClassName()))
                    {
                        final TypeTree typeTree = classPath.getTypeTree(minType);
                        if (typeTree.implementsInterface(this.resolvedMethod.getClassName())) {
                            assert (implemented == null || implemented.booleanValue());
                            implemented = Boolean.TRUE;
                        } else {
                            assert (implemented == null || !implemented.booleanValue());
                            implemented = Boolean.FALSE;
                        }

                        if (!implemented.booleanValue()) {
                            /*
                             * INVOKEINTERFACE throws an exception if the
                             * current instance does not implement the interface
                             * of the target method.
                             */
                            // TODO
                            assert (false);
                        }
                    }
                    assert (candidate != null);
                    if (target == null) {
                        target = candidate;
                    } else {
                        assert (target == candidate);
                    }
                }
            }
            targetMethod = target;
            break;
        default:
            targetMethod = null;
            assert (false) : "We can only handle static, special, virtual, and interface invocations. Perhaps there is now something like invokedynamic?";
        }
        assert (targetMethod != null);
        return targetMethod;
    }

    /**
     * INVARIANT: Shall only be used if a native method actually is called
     * @param target the invoked native method
     * @return native method which is to be called. Throws an exception if no
     * such native method is registered
     */
    private static PredefinedMethod getNativeMethod(final IMethod target, final PredefinedMethodHolder nativeMethods) {
        final PredefinedMethod nat = nativeMethods.getNativeMethod(target.getMethodIdentifier());
        return nat;
    }

    /**
     * Try to find out if this invocation is only followed by harmless opcodes
     * so that in every case the result of the invocation is returned. This is
     * useful to get around stack abstraction in case of tail recursion.
     * @param jbcOptions the JBC options
     * @return true only if the opcodes after this invocation just return the
     * result of the method invocation.
     */
    public boolean isTailCall(final JBCOptions jbcOptions) {
        if (!jbcOptions.inlineTailCalls) {
            return false;
        }
        if (this.tailCall == null) {
            // exception handling can break everything
            if (super.hasExceptionHandler()) {
                this.tailCall = Boolean.valueOf(false);
                return false;
            }
            final OpCode next = this.getNextOp();
            assert (next != null);

            // we only accept "return foo();" or "foo(); return;"
            if (!(next instanceof Return)) {
                this.tailCall = Boolean.valueOf(false);
                return false;
            }
            final Return ret = (Return) next;
            final OperandType returnType = ret.getReturnType();
            final FuzzyType fuzzyType = this.methodIdentifier.getDescriptor().getReturnType();
            if (fuzzyType == null) {
                if (returnType != null) {
                    this.tailCall = Boolean.valueOf(false);
                    return false;
                }
            }
            this.tailCall = Boolean.valueOf(true);
            return true;
        }
        return this.tailCall.booleanValue();
    }

    /**
     * @return the method identifier of the called method
     */
    public MethodIdentifier getMethodIdentifier() {
        return this.methodIdentifier;
    }

    /**
     * @return the resolved method (null if it fails)
     */
    public IMethod resolveMethod() {
        if (this.resolvedMethod == null) {
            synchronized (this) {
                if (this.resolvedMethod == null) {
                    final IClass thisParsedClass = this.getMethod().getIClass();
                    this.resolvedMethod =
                        Resolver.resolveMethodOrThrow(
                            thisParsedClass.getClassPath(),
                            this.methodIdentifier,
                            null,
                            thisParsedClass.getType(),
                            this.invocationType == InvocationType.INTERFACE);
                }
            }
        }
        return this.resolvedMethod;
    }

    /**
     * @return the invocation type
     */
    public InvocationType getInvocationType() {
        return this.invocationType;
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
        if (this.invocationType == InvocationType.DYNAMIC) {
            throw new NotYetImplementedException();
        }
        final State preEvalInst = postEvalInst.clone();
        final CallStack curInstCallStack = preEvalInst.getCallStack();
        final StackFrame curInstInvokedFrame = curInstCallStack.get(0);
        final StackFrame curInstInvokingFrame = curInstCallStack.get(1);

        //Resolve method according to §5.4.3.3 (JVMS 3rd edition).
        final IMethod resolvedMethod =
            Resolver.resolveMethodOrThrow(preEval.getClassPath(), this.methodIdentifier, null, this
                .getMethod()
                .getIClass()
                .getType(), this.invocationType == InvocationType.INTERFACE);

        if (resolvedMethod == null) {
            /*
             * The method could not be resolved. In forward-evaluation, this
             * lead to an exception, so we can just use the clone of
             * postEvalInst and just need to remove the exception stack frame
             * and unset the exception bit.
             */
            curInstCallStack.pop();
            curInstInvokingFrame.unsetException();
            return preEvalInst;
        }

        /*
         * First ensure that non-static calls have an actual object instance on
         * the stack:
         */
        final boolean isStatic = this.invocationType == InvocationType.STATIC;
        if (!isStatic) {
            final AbstractVariableReference abstrObjectRef =
                preEval
                    .getCurrentStackFrame()
                    .getOperandStack()
                    .peek(this.methodIdentifier.getDescriptor().getArgumentCount());
            final AbstractVariableReference objectRef;
            if (refMap.containsKey(abstrObjectRef)) {
                objectRef = refMap.get(abstrObjectRef);
            } else {
                objectRef = abstrObjectRef;
            }

            if (objectRef.isNULLRef()) {
                assert (preEval.getCallStack().size() != postEval.getCallStack().size());
                /*
                 * We have added the NPE constructor in this step. Remove it and the exception bit. Restore the state of
                 * the operand stack.
                 */
                curInstCallStack.pop();
                curInstInvokingFrame.unsetException();
                //Push all arguments + object ref onto the stack again:
                for (int i = this.methodIdentifier.getDescriptor().getArgumentCount(); i >= 0; i--) {
                    curInstInvokingFrame.getOperandStack().push(
                        State.mapOrCopyRef(
                            preEval,
                            preEvalInst,
                            preEval.getCurrentStackFrame().getOperandStack().peek(i),
                            refMap));
                }
                curInstInvokingFrame.setCurrentOpCode(preEval.getCurrentOpCode());

                return preEvalInst;
            }
        }

        //Check if resolved method is overwritten
        ClassPath cp = preEval.getClassPath();
        PredefinedMethodHolder predef = preEval.getTerminationGraph().getPredefinedMethods();
        if (predef.hasOverridingMethod(resolvedMethod, preEval)) {
            PredefinedMethod predefinedMethod = predef.getOverwritingMethod(resolvedMethod, preEval);
            if (predefinedMethod.isApplicable(preEval)) {
                return predefinedMethod.reverseEvaluation(preEval, postEval, postEvalInst, refMap);
            }
        }

        //Get the actual target method:
        final IMethod target = this.getTargetMethod(preEval, cp);

        //Now evaluate it, or throw an error if we aren't able to do so:
        if (target == null) {
            assert (!isStatic) : "Undefined behavior in this case";
            /*
             * The method was not found (i.e. defined as abstract and never implemented). In forward-evaluation, this
             * lead to an exception, so we can just use the clone of postEvalInst and need to remove the exception stack
             * frame and unset the exception bit. Furthermore, we need to restore the state of the operand stack.
             */
            curInstCallStack.pop();
            curInstInvokingFrame.unsetException();
            //Push all arguments + object ref onto the stack again:
            for (int i = this.methodIdentifier.getDescriptor().getArgumentCount(); i >= 0; i--) {
                curInstInvokingFrame.getOperandStack().push(
                    State.mapOrCopyRef(
                        preEval,
                        preEvalInst,
                        preEval.getCurrentStackFrame().getOperandStack().peek(i),
                        refMap));
            }
            return preEvalInst;
        }

        //Check if target method is overwritten
        if (predef.hasOverridingMethod(target, preEval)) {
            PredefinedMethod predefinedMethod = predef.getOverwritingMethod(target, preEval);
            if (predefinedMethod.isApplicable(preEval)) {
                return predefinedMethod.reverseEvaluation(preEval, postEval, postEvalInst, refMap);
            }
        }

        final boolean isTailCall = this.isTailCall(preEval.getJBCOptions());

        if (isTailCall) {
            /*
             * If this was a tail call, we need to copy over the old stackframe.
             * We then need to replace all local variables and operand stack
             * elements by useful values.
             */
            final StackFrame newSF = preEval.getCurrentStackFrame().clone();

            final AbstractVariableReference[] newLocVars = newSF.getLocalVariables().getLocalVariables();
            for (int i = 0; i < newLocVars.length; i++) {
                final AbstractVariableReference oldRef = newLocVars[i];
                final AbstractVariableReference newRef = State.mapOrCopyRef(preEval, preEvalInst, oldRef, refMap);
                newLocVars[i] = newRef;
            }

            final ArrayList<AbstractVariableReference> newOpStack = newSF.getOperandStack().getStack();
            for (int i = 0; i < newOpStack.size(); i++) {
                final AbstractVariableReference oldRef = newOpStack.get(i);
                final AbstractVariableReference newRef = State.mapOrCopyRef(preEval, preEvalInst, oldRef, refMap);
                newOpStack.set(i, newRef);
            }

            curInstCallStack.pop();
            curInstCallStack.push(newSF);
        } else {
            //Handle jlO.<init> special (as it's not really called):
            if (target.getClassName().equals(JAVA_LANG_OBJECT.getClassName())
                && target.isInstanceInitializer()
                && target.getDescriptor().getArgumentCount() == 0)
            {
                curInstInvokedFrame.getOperandStack().push(
                    State.mapOrCopyRef(
                        preEval,
                        preEvalInst,
                        preEval.getCurrentStackFrame().getOperandStack().peek(0),
                        refMap));
                curInstInvokedFrame.setCurrentOpCode(preEval.getCurrentOpCode());

                return preEvalInst;
            }

            if (target.isNative()) {
                final PredefinedMethod nat = getNativeMethod(target, preEval.getTerminationGraph().getPredefinedMethods());
                return nat.reverseEvaluation(preEval, postEval, postEvalInst, refMap);
            }

            /*
             * Remove the stack frame of the invoked method now and restore the arguments on the operand stack.
             */
            curInstCallStack.pop();

            //Push all arguments + object ref onto the stack again:
            final int argCount = target.getDescriptor().getArgumentCount();
            if (!isStatic) {
                curInstInvokingFrame.getOperandStack().push(
                    State.mapOrCopyRef(
                        preEval,
                        preEvalInst,
                        preEval.getCurrentStackFrame().getOperandStack().peek(argCount),
                        refMap));
            }
            for (int i = argCount - 1; i >= 0; i--) {
                curInstInvokingFrame.getOperandStack().push(
                    State.mapOrCopyRef(
                        preEval,
                        preEvalInst,
                        preEval.getCurrentStackFrame().getOperandStack().peek(i),
                        refMap));
            }
            curInstInvokingFrame.setCurrentOpCode(preEval.getCurrentOpCode());
        }

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return this.getMethodIdentifier().getDescriptor().getArgumentCount() + (this.getMethod().isStatic() ? 0 : 1);
    }

    @Override
    public int getNumberOfOutputs() {
        return 0;
    }

}
