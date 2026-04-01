package aprove.verification.oldframework.Syntax;


/** A symbol visitor that cares about whether a function symbol is
 *  a constructor or a def function symbol, should implement this
 *  interface.
 * @author Burak Emir
 * @version $Id$
 */

public interface FineSymbolVisitor {

    /** The variable symbol case.
     */
    public Object caseVariableSymbol(VariableSymbol vsym);

    /** The constructor symbol case.
     */
    public Object caseConstructorSymbol(ConstructorSymbol csym);

    /** The def function symbol case.
     */
    public Object caseDefFunctionSymbol(DefFunctionSymbol fsym);

    public Object caseMetaFunctionSymbol(MetaFunctionSymbol msym);

}
