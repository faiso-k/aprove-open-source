/**
 *
 * @author noschins    ki
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions.domains;

import aprove.prooftree.Export.Utility.*;


/**
 * Utility functions for integer domains.
 *
 * Valid domains are
 *   z                     - Integers ("unrestricted integers")
 *   any positive number n - signed n-bit integer with two-complements
 *                           representation ("restricted integers")
 *
 * Two <code>Domain</code> instances are considered equal iff
 * they were created for the same suffix.
 *
 *
 * FIXME: There are probably just a few different Domain instances. So add a
 * DomainFactory for singleton pattern.
 *
 * @author noschinski
 *
 */
public final class BooleanDomain extends Domain {

    public static String SUFFIX = "Booleans";

    private BooleanDomain() {
        super(BooleanDomain.SUFFIX);
    }

    protected static BooleanDomain createNew() {
        return new BooleanDomain();
    }

    @Override
    public boolean isBooleanDomain() {
        return true;
    }

    @Override
    public String export(Export_Util o) {
        return "Boolean";
    }

}
