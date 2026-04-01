package aprove.verification.oldframework.Syntax;


/** A symbol visitor that does not care about whether a function symbol is
 *  a constructor or a def function symbol, should implement this
 *  interface.
 * @author Burak Emir
 * @version $Id$
 */

public interface CoarseSymbolVisitor {

    /** The variable symbol case.
     */
    public Object caseVariableSymbol(VariableSymbol vsym);

    /** The function symbol case.
     */
    public Object caseFunctionSymbol(SyntacticFunctionSymbol fsym);

}
