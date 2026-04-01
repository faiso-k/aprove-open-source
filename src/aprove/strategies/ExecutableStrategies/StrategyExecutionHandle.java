package aprove.strategies.ExecutableStrategies;

public interface StrategyExecutionHandle {

    /**
     * stops the execution of the strategy which the handle refers to
     * @param reason must be non-null
     */
    public void stop(String reason);

    /**
     * Waits until the strategy evaluated is finished.
     */
    public void waitForFinish() throws InterruptedException;

    /**
     * Waits on finish of the execution for millis milliseconds.
     * Returns true, if the execution was finished within the given time,
     * false, otherwise.
     */
    public boolean waitForFinish(long millis) throws InterruptedException;

    /**
     * Checks whether the strategy execution is finished.
     */
    public boolean isFinished();

    /**
     * Returns the final result, if present.
     * May only be called if isFinished() delivers true.
     * @return the executable strategy that is the end of the computation.
     * May be null, if execution was aborted. Otherwise it should be
     * Fail.Fail or some Success-object.
     */
    public ExecutableStrategy getResult();
}