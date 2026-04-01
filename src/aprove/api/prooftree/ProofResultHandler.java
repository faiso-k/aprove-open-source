package aprove.api.prooftree;

/**
 * Implement this listener to be notified about the result of the analysis.
 */
public interface ProofResultHandler {

    /**
     * Called before the analysis is executed.
     */
    void onRun(ProofTreeOperationManager operationManager);

    /**
     * Called after the analysis finished successfully.
     * <p>
     * Exactly one of {@link #onSuccess(ProofTreeOperationManager, String)}, {@link #onTimeout(ProofTreeOperationManager)}
     * or {@link #onError(ProofTreeOperationManager, Exception)} is called when the analysis is done.
     * </p>
     */
    void onSuccess(ProofTreeOperationManager operationManager, String message);

    /**
     * Called after the analysis finished because the timeout was exceeded.
     * <p>
     * Exactly one of {@link #onSuccess(ProofTreeOperationManager, String)}, {@link #onTimeout(ProofTreeOperationManager)}
     * or {@link #onError(ProofTreeOperationManager, Exception)} is called when the analysis is done.
     * </p>
     */
    void onTimeout(ProofTreeOperationManager operationManager);

    /**
     * Called after the analysis finished with an error.
     * <p>
     * Exactly one of {@link #onSuccess(ProofTreeOperationManager, String)}, {@link #onTimeout(ProofTreeOperationManager)}
     * or {@link #onError(ProofTreeOperationManager, Exception)} is called when the analysis is done.
     * </p>
     */
    void onError(ProofTreeOperationManager operationManager, Exception exception);
}
