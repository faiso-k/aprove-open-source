package aprove.verification.dpframework.Orders.Utility ;

import aprove.verification.dpframework.BasicStructures.*;

/** Hashtable used for results of orders.
 *
 *  @author      Stephan Falke, Peter Schneider-Kamp
 *  @version $Id$
 */

@SuppressWarnings("serial")
public class HashOrder extends DoubleHash<TRSTerm,TRSTerm,OrderRelation> {

    private HashOrder() {
    }

    /** Creates a new instance of <code>HashOrder</code>.
     */
    public static HashOrder createHO() {
    return new HashOrder();
    }

}
