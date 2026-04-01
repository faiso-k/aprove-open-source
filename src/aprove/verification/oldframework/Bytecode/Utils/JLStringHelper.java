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
 * Collection of various methods useful in the handling of strings.
 *
 * @author Marc Brockschmidt, Carsten Otto
 */
public final class JLStringHelper {
    /**
     * Do not use me.
     */
    private JLStringHelper() {
        assert (false) : "Do not instantiate me.";
    }

    /**
     * Creates a new, completely abstracted String object in a state and adds
     * all needed annotations (i.e. possible equalities to other things
     * that might be a String) to the state.
     * @param state the state we deal with
     * @return abstract variable reference to a String object with the needed
     *  annotations.
     */
    public static AbstractVariableReference addAbstractStringToStateOrThrow(final State state) {
        /*
         * To correctly deal with possible equality, this string instance must
         * not be realized fully.
         */
        final ConcreteInstance newInstance = ConcreteInstance.newJLO(state);
        final AbstractVariableReference ref = state.createReferenceAndAdd(newInstance, OperandType.ADDRESS);
        state.getHeapAnnotations().setExistenceIsKnown(ref);
        state.setAbstractType(ref, new AbstractType(state.getClassPath(), FuzzyClassType.FT_JAVA_LANG_STRING));
        state.getHeapAnnotations().setReachableTypes(ref, new AbstractType(state.getClassPath(), FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract()));

        JLStringHelper.annotateFreshStringInstance(state, null, ref);
        return ref;
    }

    /**
     * Adds a constant string as a java.lang.String object with all fields
     * to a state (or returns an instance pointing to that string).
     *
     * This may only be used for Strings that are automatically intern()ed,
     * i.e., where it is OK to only return a reference to an existing state.
     * However, this should always be the case, as concrete Strings can only be
     * created by the ldc opcode and the initialization of field values with
     * constants, which are both automatically intern()ed.
     *
     * Thus, think on it, pray on it, find the right solution.
     *
     * @param state the state to do this to.
     * @param stringToAdd the actual string to add to the state (may not be
     *  null).
     * @return an {@link AbstractVariableReference} pointing to the String
     *  representation in the state.
     */
    public static
        AbstractVariableReference
        addConstantStringToStateOrThrow(final State state, final String stringToAdd)
    {
        if (stringToAdd == null) {
            throw new IllegalArgumentException();
        }

        final IClass parsedStringClass =
            Resolver.resolveClassOrThrow(state.getClassPath(), JAVA_LANG_STRING.getClassName(), state, null);

        if (parsedStringClass == null) {
            // not found, but some error/exception was thrown in newState
            return null;
        }

        /*
         * Find possible copy of this same string that is around in the state.
         * [This is ineffecient, we do the same iteration later on to find-non
         *  matching Strings]
         */
        final HeapAnnotations a = state.getHeapAnnotations();
        for (final AbstractVariableReference ref : state.getReferences().keySet()) {
            if (!ref.isNULLRef() && ref.pointsToInstance()) {
                final AbstractType t = a.getAbstractType(ref);
                final FuzzyClassType tType = t.getMinimalClass();
                if (tType != null && tType.equals(FuzzyClassType.FT_JAVA_LANG_STRING)) {
                    final String existingString = state.getConcreteString(ref);

                    if (existingString != null && stringToAdd.equals(existingString)) {
                        return ref;
                    }
                }
            }
        }

        final AbstractInstance newInstance = new AbstractInstance();

        final AbstractVariableReference ref = state.createReferenceAndAdd(newInstance, OperandType.ADDRESS);

        state.setConcreteString(ref, stringToAdd);

        state.getHeapAnnotations().setExistenceIsKnown(ref);
        state.setAbstractType(ref, new AbstractType(state.getClassPath(), FuzzyClassType.FT_JAVA_LANG_STRING));
        state.getHeapAnnotations().setReachableTypes(
            ref,
            new AbstractType(state.getClassPath(), new FuzzyPrimitiveType(OperandType.CHAR, 1)));

        /*
         * The problem here is that this new concrete string might be equal
         * to other, unknown strings. Add the equalities:
         */
        JLStringHelper.annotateFreshStringInstance(state, stringToAdd, ref);

        return ref;
    }

    /**
     * Add possible equalities to all other objects that might be a string.
     *
     * @param state some state.
     * @param createdString the actual, encoded String, if it exists (or null).
     * @param newRef the reference to the new String.
     */
    public static void annotateFreshStringInstance(
        final State state,
        final String createdString,
        final AbstractVariableReference newRef)
    {
        //In the competition, we don't need to support intern()
        if (state.getJBCOptions().simplifiedStringHandling()) {
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
                if (oldType.contains(FuzzyClassType.FT_JAVA_LANG_STRING, cPath, state.getJBCOptions())) {
                    /*
                     * If oRef can possibly be of the same type, we've got to
                     * add an equality annotation.
                     */
                    boolean needsEquality = true;

                    /*
                     * If we have the strings realized and they don't match,
                     * we can deduce that the strings can't be equal:
                     */
                    final FuzzyClassType tType = oldType.getMinimalClass();
                    if (createdString != null && tType != null && tType.equals(FuzzyClassType.FT_JAVA_LANG_STRING)) {
                        final String oString = state.getConcreteString(oldRef);
                        if (oString != null && !createdString.equals(oString)) {
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
