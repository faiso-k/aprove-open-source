package aprove.verification.oldframework.Syntax;


/** A variable symbol is just a special symbol.
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */

public class VariableSymbol extends Symbol {

    /* CONSTRUCTORS */

    /** Class constructor specifying name and sort. */
    private VariableSymbol(String name, Sort sort) {
    super(name, sort);
    }

    /** Public constructor specifying name and sort. */
    public static VariableSymbol create(String name, Sort sort) {
        return new VariableSymbol(name, sort);
    }

    public static VariableSymbol create(String name) {
        return new VariableSymbol(name,null);
    }

    /** Public constructor specifying name (Sort.standard)*/
    /*public static VariableSymbol create(String name) {
    return new VariableSymbol(name, Sort.standard);
    }*/

    @Override
    public Object apply(CoarseSymbolVisitor csv) {
    return csv.caseVariableSymbol(this);
    }

    @Override
    public Object apply(FineSymbolVisitor csv) {
    return csv.caseVariableSymbol(this);
    }

    @Override
    public void setSort(Sort sort) {
        this.sort = sort;
    }

    /* Change the name of this variable symbol. The sort
     *  remains unchanged.
     *
    public void rename(String name) {
        this.name = name;
    }*/ // CONSIDERED HARMFUL

    /** Return a string representation.
     */
    @Override
    public String toString() {
        return new String(this.name);
    }

    @Override
    public String verboseToString() {
    String temp = this.sort==null ? "null" : this.sort.getName();
    return "{var "+this.name+"::"+temp+"}";
    }

    public Symbol shallowcopy() {
    return new VariableSymbol(this.name, this.sort);
    }

    @Override
    public Symbol deepcopy() {
    return this.shallowcopy();
    }

    @Override
    public int getSignatureClass() {
    return Symbol.VARSIG;
    }

    @Override
    final public int hashCode() {
        return this.name.hashCode();
    }
}
