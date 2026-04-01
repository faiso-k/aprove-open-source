package aprove.verification.idpframework.Processors.ItpfRules.Execution;

/**
 *
 * @author MP
 */
public class ExecutionUid {

    public static ExecutionUid create(final boolean isDeletion) {
        return new ExecutionUid(isDeletion);
    }

    private final boolean isDeletion;

    private ExecutionUid(final boolean isDeletion) {
        this.isDeletion = isDeletion;
    }

    public boolean isDeletion() {
        return this.isDeletion;
    }

}
