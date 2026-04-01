package aprove.verification.oldframework.Bytecode.Utils;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class houses helper methods for resolving classes, fields and the like.
 *
 * @author Christian von Essen, Carsten Otto
 */
public final class Resolver {
    /**
     * Do not instantiate me.
     */
    private Resolver() {
    }

    /**
     * This method implements JVMS 5.4.3.{2|3} (Field Resolution). If field
     * resolution is successful, the corresponding field is returned. Otherwise,
     * null is returned and an error is thrown in the given state.
     * @param parsedClass the class where field resolution should start
     * @param fieldNameAndDescriptor name and descriptor of the field to look
     * for
     * @param state the current state, may be modified
     * @param accessorType the type in which the resolution was triggered
     *  through an access.
     * @return the field or null
     */
    public static Field resolveFieldOrThrow(
        final IClass parsedClass,
        final String fieldNameAndDescriptor,
        final State state,
        final TypeTree accessorType)
    {
        final Field field = parsedClass.lookupField(fieldNameAndDescriptor);
        if (field == null) {
            return Resolver.throwEx(state, NOSUCHFIELD_ERR);
        }
        // Okay, but is it accessible?
        final TypeTree referenceType = parsedClass.getType();
        if (!Resolver.isAccessibleFieldMethod(field, referenceType, accessorType)) {
            return Resolver.throwEx(state, ILLEGALACCESS_ERR);
        }
        return field;
    }

    /**
     * This method implements JVMS 5.4.3.{2|3} (Field Resolution). If field
     * resolution is successful, the corresponding field is returned. Otherwise,
     * null is returned.
     * @param parsedClass start looking for the field in here
     * @param fieldNameAndDescriptor name and descriptor of the field to look
     * for
     * @param accessorType the type in which the resolution was triggered
     *  through an access.
     * @return the resolved field if it is found and it is accessible. Null
     * otherwise.
     */
    public static Field resolveField(
        final IClass parsedClass,
        final String fieldNameAndDescriptor,
        final TypeTree accessorType)
    {
        return Resolver.resolveFieldOrThrow(parsedClass, fieldNameAndDescriptor, null, accessorType);
    }

    /**
     * This method implements JVMS 5.4.3.{1|2} (Class and Interface Resolution).
     * If the class named by the given class name can be resolved, the
     * corresponding ParsedClass object is returned. Otherwise null is returned
     * and the given state is updated with the error thrown during resolution.
     * @param cPath The considered class path for this analysis.
     * @param className Name of the class to load
     * @param state the current state, may be modified (may be null)
     * @param accessorType the type in which the resolution was triggered through an access.
     * @return ParsedClass if found, null if not found
     */
    public static IClass resolveClassOrThrow(
        final ClassPath cPath,
        final ClassName className,
        final State state,
        final TypeTree accessorType)
    {
        final IClass parsedClass = cPath.getClass(className, true);
        if (state != null && parsedClass == null) {
            if (Globals.DEBUG_MARC) {
                System.err.println("Missing class: " + className);
            }
            return Resolver.throwEx(state, Important.CLASSNOTFOUND_EXC);
        } else if (state != null && accessorType != null && !parsedClass.getType().isAccessibleFrom(accessorType)) {
            return Resolver.throwEx(state, Important.ILLEGALACCESS_ERR);
        }
        return parsedClass;
    }

    /**
     * This method implements JVMS 5.4.3.{1|2} (Class and Interface Resolution).
     * If the class named by the given class name can be resolved, the
     * corresponding ParsedClass object is returned. Otherwise null is returned.
     * @param cPath The considered class path for this analysis.
     * @param className Name of the class to load
     * @param opcode the opcode that causes this resolution
     * @return ParsedClass if found, null if not found
     */
    public static IClass resolveClass(final ClassPath cPath, final ClassName className, final OpCode opcode) {
        return Resolver.resolveClassOrThrow(cPath, className, null, opcode.getMethod().getIClass().getType());
    }

    /**
     * This method implements JVMS 5.4.3.{3|4} (Method Resolution) and
     * 5.4.3.{4|5} (Interface Method Resolution). If the method lookup is
     * successful, the corresponding ParsedMethod object is returned. Otherwise,
     * null is returned and an error is thrown in the state.
     *
     * <p><b>NOTE</b>: You may pass a null pointer as <code>state</code>
     *  argument, which simply resolves the method, without throwing an
     *  error.</p>
     *
     * @param cPath The considered class path for this analysis.
     * @param methodIdentifier the identifier of the method that should be
     * resolved
     * @param state the current state, may be modified
     * @param accessorType the type in which the resolution was triggered
     * through an access.
     * @param invokeInterface true iff the corresponding opcode is
     * INVOKEINTERFACE.
     * @return the method that is the result of method resolution or null
     */
    public static IMethod resolveMethodOrThrow(
        final ClassPath cPath,
        final MethodIdentifier methodIdentifier,
        final State state,
        final TypeTree accessorType,
        final boolean invokeInterface)
    {

        //Resolve the referenced class:
        final ClassName targetClassName = methodIdentifier.getClassName();
        final IClass targetClass = Resolver.resolveClassOrThrow(cPath, targetClassName, state, accessorType);
        if (targetClass == null) {
            return null;
        }

        /*
         * D == accessorType
         * C == TypeTree node of class containing resolved method
         */

        final TypeTree typeC = cPath.getTypeTree(methodIdentifier.getClassName());

        // 1
        if (typeC.isInterface() != invokeInterface) {
            return Resolver.throwEx(state, INCOMPATIBLECLASSCHANGE_ERR);
        }

        TypeTree typeDeclaringMethod = null;
        IMethod method = null;
        if (!invokeInterface) {
            for (final IMethod someMethod : targetClass.getMethods()) {
                if (someMethod.isSignaturePolymorphic()
                    && someMethod.getName().equals(methodIdentifier.getMethodName()))
                {
                    throw new NotYetImplementedException();
                }
            }

            // 2
            typeDeclaringMethod = typeC.findMethodUpwards(methodIdentifier);
            if (typeDeclaringMethod != null) {
                /*
                 * All super types should have been resolved by now, as we
                 * have an object of at least typeC (otherwise we couldn't
                 * call one of its methods). Therefore, we can use getClass()
                 * and don't need to use resolveClass().
                 */
                final IClass currentClass = cPath.getClass(typeDeclaringMethod.getClassName());
                method = currentClass.getLocalMethod(methodIdentifier);
            }
        }
        if (method == null) {
            // 3
            typeDeclaringMethod = typeC.findMethodUpwardsInterfaces(methodIdentifier);
            if (typeDeclaringMethod != null) {
                final IClass currentClass = cPath.getClass(typeDeclaringMethod.getClassName());
                method = currentClass.getLocalMethod(methodIdentifier);
            }
        }

        if (method == null && invokeInterface) {
            final TypeTree jlO = cPath.getTypeTree(JAVA_LANG_OBJECT.getClassName());
            if (jlO.hasLocalMethod(methodIdentifier)) {
                return cPath.getClass(jlO.getClassName()).getLocalMethod(methodIdentifier);
            }
        }

        if (method == null) {
            return Resolver.throwEx(state, NOSUCHMETHOD_ERR);
        }
        assert (typeDeclaringMethod != null) : "Could resolve method, but failed to store the declaring type";
        if (!invokeInterface) {
            if (method.isAbstract() && !typeC.isAbstract()) {
                return Resolver.throwEx(state, ABSTRACTMETHOD_ERR);
            }

            if (!Resolver.isAccessibleFieldMethod(method, typeC, accessorType)) {
                return Resolver.throwEx(state, ILLEGALACCESS_ERR);
            }
        }
        return method;
    }

    /**
     * For a non-null state, throw the exception and always return null.
     * @param state state, may be null
     * @param exception some exception to throw in state
     * @param <X> not used
     * @return null
     */
    private static <X> X throwEx(final State state, final Important exception) {
        if (state != null) {
            OpCode.throwException(state, exception);
        }
        return null;
    }

    /**
     * This method implements JVMS 5.4.4 for fields and methods.
     * @param fieldMethod the field/method, we only need the access flags and
     * the class name of the declaring type
     * @param referenceType the type used in the reference to the field/method
     * @param accessorType the type in which the resolution was triggered
     *  through an access.
     * @return true iff a method in accessorType may access the field/method
     *  <code>fieldMethod</code>
     */
    public static boolean isAccessibleFieldMethod(
        final HasAccessFlags fieldMethod,
        final TypeTree referenceType,
        final TypeTree accessorType)
    {
        final ClassName className = fieldMethod.getClassName();

        if (fieldMethod.wasMarkedAsAccessibleBy(accessorType.getClassName())) {
            return true;
        }

        if (fieldMethod.isPublic()) {
            return true;
        }

        /*
         * A mapping from our variable names to the notation used in the JVMS:
         * R == fieldMethod
         * C == className = fieldMethod.getClassName()
         *                  ("Class in which R is declared")
         * D == accessorType
         * T == referenceType
         */

        if (fieldMethod.isProtected() && accessorType.isSubClassOf(className)) {
            if (fieldMethod.isStatic()) {
                return true;
            }
            return referenceType.isProperSubClassOf(accessorType.getClassName())
                || referenceType.equals(accessorType)
                || accessorType.isProperSubClassOf(referenceType.getClassName());
        }
        if (!fieldMethod.isPrivate() && !fieldMethod.isPublic()) {
            // protected or default
            return className.getPkgName().equals(accessorType.getClassName().getPkgName());
        }
        if (fieldMethod.isPrivate()) {
            return className.equals(accessorType.getClassName());
        }
        return false;
    }
}
