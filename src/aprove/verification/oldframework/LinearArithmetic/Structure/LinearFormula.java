package aprove.verification.oldframework.LinearArithmetic.Structure;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public abstract class LinearFormula {

    //method for visitor pattern
    public abstract <T> T apply( LinearFormulaVisitor<T> fv );

    public abstract LinearFormula deepcopy();

    @Override
    public abstract String toString();
}
