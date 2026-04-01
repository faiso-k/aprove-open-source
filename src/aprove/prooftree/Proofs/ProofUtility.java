package aprove.prooftree.Proofs;

import aprove.prooftree.Export.Utility.*;

/**
 * Created on 27.05.2005 by marmer
 *
 * Some helpful functions to generate a nice proof output.
 *
 * @author marmer
 * @version $Id$
 */

public class ProofUtility {

    /**
     * Nice notation for TRS R.
     */
    public static final String R(Export_Util o, String str) {
        return o.math(o.calligraphic(str));
    }

    /**
     * Nice notation for String "Term Rewriting System".
     */
    public static final String TRS(Export_Util o) {
        return o.bold("Term Rewriting System");
    }

    /**
     * Nice notation for String "Conditional Term Rewriting System".
     */
    public static final String CTRS(Export_Util o) {
        return o.bold("Conditional Term Rewriting System");
    }
}
