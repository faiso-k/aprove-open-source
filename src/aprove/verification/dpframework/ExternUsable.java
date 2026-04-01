package aprove.verification.dpframework;

import aprove.prooftree.Obligations.*;

/**
 * <p>An {@link BasicObligation} implementing this interface can emit itself in a
 * text format which can be read by AProVE. This format SHOULD be the same
 * as the usual input format for this Obligation. Parsing this text yields
 * an Obligation which is the same as the emitting one.</p>
 *
 * <p>Intended use cases:</p>
 * <ul>
 * <li><em>External processors</em>: Export this problem to give it to an
 * arbitrary external program, which processes this problem.</li>
 * <li><em>Extracting problems from a proof</em>:
 * While implementing or debugging new processors, it is often useful to
 * just investigate one of the problems which are created during the proof.
 * For this reason there should be a possibility to save this specific problem
 * as text file to be able to continue from this point later on.</li>
 * </ul>
 *
 * (Documentation by noschinski)
 * @author swiste
 * @version $Id$
 *
 */

public interface ExternUsable {

    /**
     * Returns a text representation like described in the class documentation.
     *
     * @throws NotExternUsableInstanceException if the instance cannot be converted
     *      to a String.
     */
    String toExternString() throws NotExternUsableInstanceException;

    /**
     * Returns the file extension associated with the text representation
     * returned by <code>toExternString</code>.
     */
    String externName();
}
