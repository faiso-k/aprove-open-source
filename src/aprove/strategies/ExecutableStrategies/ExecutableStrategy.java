package aprove.strategies.ExecutableStrategies;

/**
 * the class of executable strategies corresponding to
 * the definition described in doc/processors/processors2
 * @author thiemann
 *
 */
public abstract class ExecutableStrategy {

    protected final RuntimeInformation rti;

    public ExecutableStrategy(RuntimeInformation rti) {
        this.rti = rti;
    }

    /**
     * checks whether a strategy is fully reduced to normal form.
     *
     * In other words, true if calling exec() makes no sense anymore.
     */
    public boolean isNormal() {
        return false;
    }

    /**
     * checks whether a strategy is halted in a failure state.
     */
    public boolean isFail() {
        return false;
    }

    /**
     * Evaluates the strategy a bit, possibly doing parallel reduction.
     *
     * Attempting to call this method on a strategy where isNormal() returns true
     * will result in a runtime exception.
     *
     * Otherwise, this method should return the ExecutableStrategy
     * that resulted from evaluation, or null if nothing could be done at this time.
     *
     * In the former case, exec() will be called shortly on the new strategy,
     * in the latter strategy execution may sleep until something interesting happens.
     *
     * See ExecRepeat.exec() for a realistic example.
     *
     * This method is guaranteed to be called from the machine thread, so you
     * can modify the proof tree, but you should not do any operation that
     * may take a long time to complete, and you should not throw exceptions.
     */
    abstract ExecutableStrategy exec();

    /**
     * stops a strategy, i.e., all processors that are
     * running inside this strategy will be stopped
     */
    abstract void stop(String reason);

    /**
     * for debug output
     */
    @Override
    public abstract String toString();
}
