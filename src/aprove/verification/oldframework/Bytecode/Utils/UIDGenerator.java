package aprove.verification.oldframework.Bytecode.Utils;

/**
 * A convenience class to generate unique names for our variables.
 * @author Christian von Essen
 */
public class UIDGenerator {
    /**
     * Prefix for the names to be generated.
     */
    private final String uidPrefix;

    /**
     * Counter used to generate unique names.
     */
    private long id;

    /**
     * Statically provided generator for unique names for integer variables.
     */
    private static UIDGenerator intUIDGenerator = new UIDGenerator("i");

    /**
     * Statically provided generator for unique names for float variables.
     */
    private static UIDGenerator floatUIDGenerator = new UIDGenerator("f");

    /**
     * Statically provided generator for unique names for object instances.
     */
    private static UIDGenerator objectUIDGenerator = new UIDGenerator("o");

    /**
     * Statically provided generator for unique names for object instances.
     */
    private static UIDGenerator arrayUIDGenerator = new UIDGenerator("a");

    /**
     * Statically provided generator for unique names for llvm value instances.
     */
    private static UIDGenerator valueUIDGenerator = new UIDGenerator("v");

    /**
     * Create a new uid generator using the parameter as prefix for generated
     * names.
     * @param prefix prefix of all generated names.
     */
    public UIDGenerator(final String prefix) {
        this.uidPrefix = prefix;
        this.id = 1;
    }

    /**
     * @return the next unique name.
     */
    public final synchronized String next() {
        return this.uidPrefix + this.id++;
    }

    /**
     * @return generator for unique integer variables.
     */
    public static final UIDGenerator getIntUIDGenerator() {
        return UIDGenerator.intUIDGenerator;
    }

    /**
     * @return generator for unique float variables.
     */
    public static final UIDGenerator getFloatUIDGenerator() {
        return UIDGenerator.floatUIDGenerator;
    }

    /**
     * @return generator for unique object instance variables.
     */
    public static final UIDGenerator getObjectUIDGenerator() {
        return UIDGenerator.objectUIDGenerator;
    }

    /**
     * @return generator for unique array instance variables.
     */
    public static final UIDGenerator getArrayUIDGenerator() {
        return UIDGenerator.arrayUIDGenerator;
    }

    /**
     * @return generator for unique value variables.
     */
    public static final UIDGenerator getValueUIDGenerator() {
        return UIDGenerator.valueUIDGenerator;
    }
}
