package aprove.verification.oldframework.Bytecode.Parser;

/**
 * This class contains all information necessary to identify a method, i.e.
 * the class it belongs to, its actual name and its descriptor.
 *
 * @author Christian von Essen
 */
public class MethodIdentifier {
    /**
     * The name of the enclosing class.
     */
    private final ClassName className;

    /**
     * The name of this method.
     */
    private final String methodName;

    /**
     * The descriptor of this method.
     */
    private final ParsedMethodDescriptor descriptor;

    /**
     * Creates a new method identifier.
     * @param classN The name of the enclosing class.
     * @param methodN The name of this method.
     * @param desc The descriptor of this method.
     */
    public MethodIdentifier(final ClassName classN, final String methodN, final ParsedMethodDescriptor desc) {
        this.className = classN;
        this.methodName = methodN;
        this.descriptor = desc;
    }

    /**
     * @return The name of the enclosing class.
     */
    public ClassName getClassName() {
        return this.className;
    }

    /**
     * @return The name of this method.
     */
    public String getMethodName() {
        return this.methodName;
    }

    /**
     * @return The descriptor of this method.
     */
    public ParsedMethodDescriptor getDescriptor() {
        return this.descriptor;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object o) {
        if (!(o instanceof MethodIdentifier)) {
            return false;
        }

        final MethodIdentifier m = (MethodIdentifier) o;
        return this.className.equals(m.getClassName())
            && this.methodName.equals(m.getMethodName())
            && this.descriptor.equals(m.getDescriptor());
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return this.className.hashCode() ^ this.methodName.hashCode() ^ this.descriptor.hashCode();
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.className + "." + this.methodName + this.descriptor;
    }
}
