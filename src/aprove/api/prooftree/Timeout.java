package aprove.api.prooftree;

import java.util.*;

/**
 * Represents the (possibly infinite) timeout for the analysis.
 */
public class Timeout {

    private static final int INTERNAL_INFINITE = 0;
    private static final int SERIALIZED_INFINITE = 0;

    /**
     * @return A Timeout with the given duration
     * or an infinite Timeout for a number <= 0
     * or an infinite Timeout for the empty String
     * or an empty Optional for a string that is not a number.
     */
    public static Optional<Timeout> fromStringInSeconds(String string) {
        Objects.requireNonNull(string);
        String trimmed = string.trim();
        if (trimmed.isEmpty()) {
            return Optional.of(infinite());
        } else {
            return tryParseInt(trimmed).map(d -> d * 1000).map(Timeout::positiveOrInfinite);
        }
    }

    private static Optional<Integer> tryParseInt(String text) {
        try {
            return Optional.of(Integer.valueOf(text));
        } catch (final NumberFormatException e) {
            return Optional.empty();
        }
    }

    /**
     * Deserializes an int value to a Timeout.
     * 
     * @see Timeout#serialize()
     */
    public static Optional<Timeout> deserialize(int serializedMillis) {
        if (serializedMillis == SERIALIZED_INFINITE) {
            return Optional.of(infinite());
        } else {
            return positive(serializedMillis);
        }
    }

    /**
     * @return A non-infinite Timeout if the parameter is positive. An infinite Timeout if the parameter is <= 0.
     */
    public static Timeout positiveOrInfinite(int durationInMillis) {
        return positive(durationInMillis).orElseGet(Timeout::infinite);
    }

    /**
     * @return An infinite Timeout.
     */
    public static Timeout infinite() {
        return new Timeout(INTERNAL_INFINITE);
    }

    /**
     * @return A non-infinite Timeout if the parameter is positive. An empty Optional if the parameter is <= 0.
     */
    public static Optional<Timeout> positive(int durationInMillis) {
        if (isInternalInfinite(durationInMillis)) {
            return Optional.empty();
        } else {
            return Optional.of(new Timeout(durationInMillis));
        }
    }

    private static boolean isInternalInfinite(int durationInMillis) {
        return durationInMillis <= INTERNAL_INFINITE;
    }

    private final int durationInMillis;

    private Timeout(int durationInMillis) {
        this.durationInMillis = durationInMillis;
    }

    public boolean isInfinite() {
        return isInternalInfinite(durationInMillis);
    }

    public int getDurationOr(int ifIsInfinite) {
        return isInfinite() ? ifIsInfinite : this.durationInMillis;
    }

    public int getDurationOrThrow() {
        if (isInfinite()) {
            throw new IllegalStateException("duration is infinite");
        } else {
            return this.durationInMillis;
        }
    }

    /**
     * Serializes this Timeout to an int value.
     * 
     * @see Timeout#deserialize(int)
     */
    public int serialize() {
        return getDurationOr(SERIALIZED_INFINITE);
    }
}
