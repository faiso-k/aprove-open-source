package aprove.strategies.Abortions;

import java.util.*;

import aprove.strategies.ExecutableStrategies.*;

public abstract class AbortionFactory {
    /**
     * Creates a new dummy abortion without any attached clocks.
     *
     * Suitable for testing, or when CPU time is irrelevant.
     */
    public static Abortion create() {
        return new Abortion(Collections.<Clock>emptyList());
    }

    /**
     * Creates a new abortion which reports to the given clock.
     *
     * Suitable for very simplistic pseudo-strategies in custom mains.
     */
    public static Abortion create(final Clock clock) {
        return new Abortion(Collections.singletonList(clock));
    }

    /**
     * Creates a new abortion with settings as configured in
     * the given RuntimeInformation.
     *
     * This method is used by the regular processor executor.
     */
    public static Abortion create(final RuntimeInformation rti) {
        // rti.getClocks() is guaranteed to be unmodifiable.
        return new Abortion(rti.getClocks());
    }

    /**
     * Creates a new abortion which reports to any number of clocks.
     */
    public static Abortion create(final Clock... clocks) {
        List<Clock> clockList = Arrays.asList(clocks);
        // Copy list to ensure no caller modifications happen
        clockList = new ArrayList<>(clockList);
        // And wrap in unmodifiable so clients cannot modify it either.
        clockList = Collections.unmodifiableList(clockList);
        return new Abortion(clockList);
    }
}
