package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;

public interface RuntimeInformation {
    /**
     * Creates a copy of this RuntimeInformation that also accounts CPU time
     * to the passed clock.
     *
     * Cheap operation.
     */
    public RuntimeInformation copyAddClock(Clock clock);

    public RuntimeInformation copyWithDifferentScheduling(ThreadingPolicy policy);

    /**
     * Returns all clocks that CPU time should be accounted to.
     *
     * The returned list is unmodifiable and never modified,
     * so it can be safely iterated over without synchronization.
     *
     * (It is not an ImmutableList because the contained Clocks are
     * not immutable at all.)
     */
    public List<Clock> getClocks();

    public ThreadingPolicy getThreadingPolicy();

    public Object getMetadata(Metadata key);

    public StrategyProgram getProgram();

    public void execute();

    public boolean checkProofs();
}
