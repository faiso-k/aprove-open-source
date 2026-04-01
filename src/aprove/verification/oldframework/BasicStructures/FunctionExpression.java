package aprove.verification.oldframework.BasicStructures;

/**
 * A function expression has a function symbol and is no variable. If it is a compound expression, the number of its
 * arguments must match the arity of its function symbol. If it is a constant and non-variable expression, the arity of
 * its function symbol must be 0.
 * @author cryingshadow
 * @version $Id$
 */
public interface FunctionExpression extends Expression, HasRootSymbol, HasArity {

    @Override
    default int getArity() {
        return this.getRootSymbol().getArity();
    }

    @Override
    default String getName() {
        return this.getRootSymbol().getName();
    }

}
