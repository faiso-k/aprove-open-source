package aprove.verification.oldframework.BasicStructures;

/**
 * Objects with a root symbol can return that symbol.
 * For example, for a Term t=f(t_1, ..., t_n) we have root(t) = f 
 * and for a rule l -> r we have root(l -> r) = root(l).
 * Created on 12.04.2005.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public interface HasRootSymbol {

    /**
     * @return The FunctionSymbol being the root symbol of this FunctionExpression (i.e., root(f(t_1, ..., t_n)) = f).
     *         Must not be null.
     */
    public FunctionSymbol getRootSymbol();

}
