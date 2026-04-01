package aprove.verification.dpframework.Utility;

/**
 * <p>A name provider for a *Problem provides all names having predefined semantics
 * for this kind of *Problem.</p>
 *
 * <p>We cannot just use the set interface, because it does not work well with an infinite
 * number of names, like e.g. ITRSProblem and CLSProblem have (as they provide integers).
 * </p>
 *
 * @author noschinski
 * @version $Id$
 */
public interface NameProvider {

    /**
     * Checks if a symbol with name <code>name</code> has predefined semantics.
     */
    boolean contains(String name);
}
