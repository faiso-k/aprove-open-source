package aprove.verification.dpframework.Orders;

import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Abstract superclass for accessing and exporting
 * path orders with quasi-precedence.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
abstract public class AbstractQuasiPO extends AbstractPathOrder {

    protected Qoset<FunctionSymbol> precedence;

    @Override
    public Qoset<FunctionSymbol> getPrecedence() {
        return this.precedence;
    }

}
