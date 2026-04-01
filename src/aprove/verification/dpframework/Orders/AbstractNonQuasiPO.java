package aprove.verification.dpframework.Orders;

import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Abstract superclass for accessing and exporting
 * path orders without quasi-precedence.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
abstract public class AbstractNonQuasiPO extends AbstractPathOrder {

    protected Poset<FunctionSymbol> precedence;

    @Override
    public Poset<FunctionSymbol> getPrecedence() {
        return this.precedence;
    }

}
