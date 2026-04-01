package aprove.verification.oldframework.Utility.SMTUtility;

/**
 * Generate new unique names with a given prefix for YICES input
 *
 * @author Andreas Kelle-Emden
 */
public class YICESNameGenerator {

    protected String prefix = null;
    protected long num = 0;

    private YICESNameGenerator(String prefix) {
        this.prefix = prefix;
    }

    /**
     * Create and return a new instance for the given prefix
     * if the prefix is okay for YICES input.
     * Otherwise return null.
     */
    public static YICESNameGenerator create(String prefix) {
        if (prefix.length() == 0) {
            return null;
        }
        if (prefix.contains(":")) {
            return null;
        }
        return new YICESNameGenerator(prefix);
    }

    /**
     * Create and return next new name.
     */
    public synchronized String getNewName() {
        this.num++;
        return this.prefix + this.num;
    }
}
