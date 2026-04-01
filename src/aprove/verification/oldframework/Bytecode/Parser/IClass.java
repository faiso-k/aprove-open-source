package aprove.verification.oldframework.Bytecode.Parser;

import java.util.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public interface IClass {

    ClassStreamProvider.Type getClassStreamProviderType();

    /**
     * @return the fully qualified name of the parsed class
     */
    ClassName getClassName();

    /**
     * Searches for a specified method with a fixed call descriptor only in this
     * class.
     * @param methodName name of a method
     * @param callDescriptor string representation of the method's descriptor
     * @return the corresponding parsed method, if it could be found
     */
    IMethod getLocalMethod(String methodName, ParsedMethodDescriptor callDescriptor);

    /**
     * Searches for a specified method with a fixed call descriptor only in this
     * class.
     * @param id Method id
     * @return
     */
    IMethod getLocalMethod(MethodIdentifier id);

    /**
     * @return the program in which this class is used
     */
    ClassPath getClassPath();

    /**
     * @return the type of the super class
     */
    TypeTree getSuperType();

    /**
     * @return all known methods
     */
    Collection<IMethod> getMethods();

    /**
     * @return the type tree of this class
     */
    TypeTree getType();

    /**
     * Look at all super classes until the method is found.
     * @param resolvedMethodId package, class and method name, signature of the
     *  method to invoke.
     * @return the method defined by the given name and descriptor
     */
    public default IMethod getOverridingMethod(final MethodIdentifier resolvedMethodId) {
        IClass currentClass = this;

        /*
         * C == this
         * A == resolvedMethodId.getClassName()
         * m2 ~= resolvedMethodId
         * m1 (might be methodCandidate) is to be returned
         *
         * We don't follow the specification (JVMS 3rd edition, draft from May
         * 2009) here, as we suspect it's wrong: No checks on the access
         * flags of methodCandidate (m1) are done, thus the spec would allow
         * even a private m1 to override a given m2 (which is public). The
         * actual Sun JVM invokes m2 (seen by testing this), thus the spec
         * is probably wrong here.
         *
         * To get the specified behaviour, do the access bit checks on
         * resolvedMethod instead of methodCandidate.
         */

        if (Globals.useAssertions) {
            final TypeTree thisType = this.getType();
            final ClassName resolvedClass = resolvedMethodId.getClassName();
            assert (thisType.isSubClassOf(resolvedClass) || thisType.implementsInterface(resolvedClass));
        }

        while (currentClass != null) {
            final IMethod methodCandidate = currentClass.getLocalMethod(resolvedMethodId);
            if (methodCandidate != null && !methodCandidate.isPrivate()) {
                if (methodCandidate.isPublic()
                        || methodCandidate.isProtected()
                        || resolvedMethodId.getClassName().getPkgName().equals(currentClass.getClassName().getPkgName()))
                {
                    return methodCandidate;
                }
            }

            //Couldn't find method in this class, travel the type tree upwards:
            final TypeTree superTypeTree = currentClass.getSuperType();
            if (superTypeTree == null) {
                //We have no super type, so we are probably Object:
                break;
            }
            currentClass = this.getClassPath().getClass(currentClass.getSuperType().getClassName());
        }

        return null;
    }

    /**
     * Look at all super classes until the method is found.
     * @param resolvedMethodId package, class and method name, signature of the
     *  method to invoke.
     * @return the method defined by the given name and descriptor
     */
    IMethod getMethodRecursively(MethodIdentifier resolvedMethodId);

    /**
     * @return all static fields
     */
    ImmutableMap<String, Field> getStaticFields();

    /**
     * @return all instance fields
     */
    ImmutableMap<String, Field> getInstanceFields();

    /**
     * @param fieldNameAndDescriptor name and descriptor of the field
     * @return the (instance or static) field with the given name and
     * descriptor.
     */
    Field getField(String fieldNameAndDescriptor);

    /**
     * Implements the lookup procedure of JVMS 5.4.3.{2|3} (points 1 to 4).
     * @param fieldNameAndDescriptor the name of the field to find
     * @return the field object or null
     */
    public default Field lookupField(final String fieldNameAndDescriptor) {
        // start with a local lookup
        Field result = getField(fieldNameAndDescriptor);
        if (result != null) {
            return result;
        }
        for (final TypeTree implementedInterface : this.getType().getImplementedInterfaces()) {
            final IClass pc = this.getClassPath().getClass(implementedInterface.getClassName());
            result = pc.lookupField(fieldNameAndDescriptor);
            if (result != null) {
                return result;
            }
        }
        final TypeTree superType = this.getType().getSuperType();
        if (superType != null) {
            final IClass pc = this.getClassPath().getClass(superType.getClassName());
            return pc.lookupField(fieldNameAndDescriptor);
        }
        return null;
    }

    /**
     * @return true iff this is a final class.
     */
    boolean isFinal();

    /**
     * @return true iff the class is final or if it does not have any subtypes
     */
    boolean isEffectivelyFinal();

    /**
     * @return the class file version, as pair (majorVersion, minorVersion).
     */
    Pair<Integer, Integer> getClassFileVersion();

}
