package aprove.api.prooftree;

/**
 * The operation manager provides information about the currently running analysis. It can also be used to stop all currently running analysis.
 */
public interface ProofTreeOperationManager {

    void stop();

    boolean isRunning();
}
