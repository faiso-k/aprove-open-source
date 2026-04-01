package aprove.verification.oldframework.Bytecode.Parser;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * This class parses the method signatures used in java bytecode;
 *
 * @author Christian von Essen
 */
public class ParsedMethodDescriptor {
    /**
     * List of argument types for this method signature (from the left to right)
     */
    private final ArrayList<FuzzyType> types;

    /**
     * Type of the return value.
     */
    private final FuzzyType returnType;

    /**
     * This is only used for toString. Maybe we can replace it?
     */
    private final String methodSignatureString;

    /**
     * Construct a new method signature from a string (based on the JVMS standard).
     * @param string method string.
     */
    public ParsedMethodDescriptor(final String string) {
        this.methodSignatureString = string;

        this.types = new ArrayList<>();
        final int argumentsStart = string.indexOf('(') + 1;
        final int argumentsEnd = string.indexOf(')', argumentsStart);

        if (argumentsStart == -1 || argumentsEnd == -1) {
            throw new RuntimeException("Not a method signature: " + string);
        }

        int i = argumentsStart;
        while (i != argumentsEnd) {
            final FuzzyType type = FuzzyType.parseTypeDescriptor(string.substring(i));
            this.types.add(type);
            i += type.typeSignatureLength();
        }

        if (string.charAt(argumentsEnd + 1) != 'V') {
            this.returnType = FuzzyType.parseTypeDescriptor(string.substring(argumentsEnd + 1));
        } else {
            this.returnType = null;
        }
    }

    /**
     * @return number of arguments in this method signature.
     */
    public int getArgumentCount() {
        return this.types.size();
    }

    /**
     * @param i index of an argument
     * @return Type of the <code>i</code>th argument of this method signature.
     */
    public FuzzyType getType(final int i) {
        if (i < 0 || i >= this.types.size()) {
            throw new IndexOutOfBoundsException();
        }

        return this.types.get(i);
    }

    /**
     * @return number of words (32 bits) used up by the arguments for this method.
     */
    public int getArgumentWords() {
        int words = 0;
        for (final FuzzyType t : this.types) {
            words += t.getUsedWords();
        }
        return words;
    }

    /**
     * @return null if the return type is void, otherwise the type
     */
    public FuzzyType getReturnType() {
        return this.returnType;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.methodSignatureString;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object o) {
        if (!(o instanceof ParsedMethodDescriptor)) {
            return false;
        }

        return this.methodSignatureString.equals(((ParsedMethodDescriptor) o).methodSignatureString);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.methodSignatureString.hashCode();
    }
}
