package aprove.verification.oldframework.Bytecode.Utils;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import aprove.input.Programs.jbc.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;

/**
 * Collection of various methods useful in the handling of class objects.
 *
 * @author Marc Brockschmidt, Carsten Otto
 */
public final class JLClassHelper {
    /**
     * Do not use me.
     */
    private JLClassHelper() {
        assert (false) : "Do not instantiate me.";
    }

    /**
     * Creates a new, completely abstracted Class object in a state and adds
     * all needed annotations (i.e. possible equalities to other things
     * that might be a Class object) to the state.
     * @param state the state we deal with
     * @return abstract variable reference to a Class object with the needed
     *  annotations.
     */
    public static AbstractVariableReference addAbstractClassToStateOrThrow(final State state) {
        /*
         * To correctly deal with possible equality, this string instance must
         * not be realized fully.
         */
        final ConcreteInstance newInstance = ConcreteInstance.newJLO(state);
        final AbstractVariableReference ref = state.createReferenceAndAdd(newInstance, OperandType.ADDRESS);
        state.getHeapAnnotations().setExistenceIsKnown(ref);
        state.setAbstractType(ref, new AbstractType(state.getClassPath(), FuzzyClassType.FT_JAVA_LANG_CLASS));
        state.getHeapAnnotations().setReachableTypes(
            ref,
            new AbstractType(state.getClassPath(), new FuzzyClassType(FuzzyClassType.FT_JAVA_LANG_OBJECT
                .getMinimalClass(), false)));

        annotateFreshClassInstance(state, null, ref);
        return ref;
    }

    /**
     * Adds a constant class as a java.lang.Class object with all fields
     * to a state (or returns an instance pointing to a fitting Class object).
     *
     * @param state the state to do this to.
     * @param typeToAdd the actual string to add to the state (may not be
     *  null).
     * @return an {@link AbstractVariableReference} pointing to the String
     *  representation in the state.
     */
    public static
        AbstractVariableReference
        addConstantClassToStateOrThrow(final State state, final FuzzyType typeToAdd)
    {
        if (typeToAdd == null) {
            throw new IllegalArgumentException();
        }

        final IClass parsedClassClass =
            Resolver.resolveClassOrThrow(state.getClassPath(), JAVA_LANG_CLASS.getClassName(), state, null);

        if (parsedClassClass == null) {
            // not found, but some error/exception was thrown in newState
            return null;
        }

        /*
         * Find possible copy of this same Class object that is around in
         * the state.
         * [This is ineffecient, we do the same iteration later on to find-non
         *  matching Strings]
         */
        final HeapAnnotations a = state.getHeapAnnotations();
        for (final AbstractVariableReference ref : state.getReferences().keySet()) {
            if (!ref.isNULLRef() && ref.pointsToInstance()) {
                final AbstractType t = a.getAbstractType(ref);
                final FuzzyClassType tType = t.getMinimalClass();
                if (tType != null && tType.equals(FuzzyClassType.FT_JAVA_LANG_CLASS)) {
                    final FuzzyType existingClassName = state.getClassInstance(ref);

                    if (existingClassName != null && typeToAdd.equals(existingClassName)) {
                        return ref;
                    }
                }
            }
        }

        //Create fresh instance
        final AbstractInstance newInstance = new AbstractInstance();

        final AbstractVariableReference ref = state.createReferenceAndAdd(newInstance, OperandType.ADDRESS);

        state.setClassInstance(ref, typeToAdd);

        state.getHeapAnnotations().setExistenceIsKnown(ref);
        state.getHeapAnnotations().setReachableTypes(
            ref,
            new AbstractType(state.getClassPath(), new FuzzyClassType(FuzzyClassType.FT_JAVA_LANG_OBJECT
                .getMinimalClass(), false)));
        state.setAbstractType(ref, new AbstractType(state.getClassPath(), FuzzyClassType.FT_JAVA_LANG_CLASS));

        /*
         * The problem here is that this new concrete string might be equal
         * to other, unknown strings. Add the equalities:
         */
        annotateFreshClassInstance(state, typeToAdd, ref);

        return ref;
    }

    /**
     * Add possible equalities to all other objects that might be a string.
     *
     * @param state some state.
     * @param createdType the name of the created Class (if it exists, or null)).
     * @param newRef the reference to the new String.
     */
    public static void annotateFreshClassInstance(
        final State state,
        final FuzzyType createdType,
        final AbstractVariableReference newRef)
    {
        //In the competition, we don't need to support .getClass()
        if (state.getJBCOptions().simplifiedClassHandling()) {
            return;
        }

        final HeapAnnotations a = state.getHeapAnnotations();
        final EqualityGraph equalityGraph = a.getEqualityGraph();
        final ClassPath cPath = state.getClassPath();

        for (final AbstractVariableReference oldRef : state.getReferences().keySet()) {
            if (newRef == oldRef || oldRef.isNULLRef()) {
                continue;
            }
            final AbstractType oldType = a.getAbstractType(oldRef);
            if (oldRef.pointsToInstance()) {
                if (oldType.contains(FuzzyClassType.FT_JAVA_LANG_CLASS, cPath, state.getJBCOptions())) {
                    /*
                     * If oRef can possibly be of the same type, we've got to
                     * add an equality annotation.
                     */
                    boolean needsEquality = true;

                    /*
                     * If we have the classes realized and they don't match,
                     * we can deduce that the strings can't be equal:
                     */
                    final FuzzyClassType tType = oldType.getMinimalClass();
                    if (createdType != null && tType != null && tType.equals(FuzzyClassType.FT_JAVA_LANG_CLASS)) {
                        final FuzzyType c = state.getClassInstance(oldRef);
                        if (c != null && !createdType.equals(c)) {
                            needsEquality = false;
                        }
                    }
                    if (needsEquality) {
                        equalityGraph.addPossibleEquality(state, newRef, oldRef);
                    }
                }
            }
        }
    }
}
