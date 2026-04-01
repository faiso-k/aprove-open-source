package aprove.verification.oldframework.IntTRS.PoloRedPair;

/**
 * This should tell the processor, which kind of bounds are preferred,
 * if both are available.
 * @author Matthias Hoelzel
 */
public enum BoundBehavior {
    PREFER_UPPER_BOUNDS, PREFER_LOWER_BOUNDS, PREFER_RANDOM_BOUNDS;
}
