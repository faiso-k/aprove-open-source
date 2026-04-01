package aprove.strategies.Parameters;


/**
 * Used to mark a class that normally does lazy initialization.
 *
 * This interface helps us write a user-friendly interface,
 * because it allows us to trigger lazy initialization early.
 * This lets us check for errors thoroughly when user errors are to be expected.
 *
 * Alternatively, ignoring this interface may give some speedup through lazy
 * initialization, for a competition setting.
 */
public interface EagerlyCheckable {
    /**
     * Attempts to initialize everything now, instead of lazily.
     *
     * Implementors should try to initialize as much as possible,
     * so errors show up when this is called, instead of at runtime.
     * Note that there is no guarantee that this method will ever be called.
     */
    public void check(StrategyProgram program);
}
