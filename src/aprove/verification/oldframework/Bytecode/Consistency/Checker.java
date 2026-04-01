package aprove.verification.oldframework.Bytecode.Consistency;

public interface Checker {
    /**
     * @return true iff the check succeedes, i.e. the graph passes the check
     */
    public boolean check();
}
