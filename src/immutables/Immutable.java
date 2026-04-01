package immutables;

/**
 * Implement this interface to indicate immutability.
 * <p>
 * An object is immutable if there is no operation
 * such that its equals or hashCode behavior is changed.
 * <p>
 * Note, however, that this does not guarantee real immutability. Objects within the data structure can still be 
 * modified (but should not). Whenever a supported method of an immutable data structure is called, its consistency is 
 * checked (at least in the immutables project).
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public interface Immutable {
    
    /**
     * Are we using the more mutable versions without checks?
     */
    public static final boolean MUTABLES = true;
    
}
