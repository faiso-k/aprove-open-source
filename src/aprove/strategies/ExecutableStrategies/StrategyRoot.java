package aprove.strategies.ExecutableStrategies;

public class StrategyRoot {
    private ExecutableStrategy exStr;

    public StrategyRoot(ExecutableStrategy exStr) {
        if (exStr == null) {
            throw new NullPointerException("exStr");
        }
        this.exStr = exStr;
    }

    public ExecutableStrategy getExStr() {
        return this.exStr;
    }

    /**
     * Evaluates the strategy one step.
     *
     * Returns true if further evaluation is wanted right now,
     * false if calling this again right now would be pointless.
     *
     * Effectively, this is to be called similar to
     *
     * <pre>
     * while(! root.getExStr().isNormal()) {
     *   while(root.evaluateOnce())
     *     ; // Loop
     *
     *   Thread.sleep(100);
     * }
     * </pre>
     */
    public boolean evaluateOnce() {
        ExecutableStrategy newStrategy = this.exStr.exec();

        if (newStrategy == null) {
            return false;
        }

        this.exStr = newStrategy;
        return true;
    }

    public void stop(String reason) {
        this.exStr.stop(reason);
    }
}
