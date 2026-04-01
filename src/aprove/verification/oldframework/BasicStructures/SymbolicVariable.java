package aprove.verification.oldframework.BasicStructures;

/**
 * A SymbolicVariable is used in symbolic evaluation graphs.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class SymbolicVariable extends VariableSkeleton {

    /**
     * A debug name (e.g., when merging two SymbolicVariables, this might hold the two names of them).
     */
    private final String debugName;

    /**
     * @param name The name.
     */
    public SymbolicVariable(String name) {
        super(name);
        this.debugName = name;
    }

    /**
     * @param name The name.
     * @param debug The debug name.
     */
    public SymbolicVariable(String name, String debug) {
        super(name);
        this.debugName = debug;
    }

    /**
     * @return The debug name.
     */
    public String getDebugName() {
        return this.debugName;
    }

}
