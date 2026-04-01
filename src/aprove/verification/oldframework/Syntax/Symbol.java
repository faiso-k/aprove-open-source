package aprove.verification.oldframework.Syntax;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;

/** A sorted symbol.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

public abstract class Symbol extends UnsortedSymbol implements Checkable, HTML_Able, LaTeX_Able {
    public static String IF_SYMBOL = "IF";
    /** Sort of this symbol. */
    protected Sort sort;

    // The signature-classes
    public static final int DEFAULTSIG = 0;
    public static final int MAINSIG = 1;
    public static final int BOOLSIG = 2;
    public static final int SELECTORSIG = 3;
    public static final int VARSIG = 10;
    public static final int CONSSIG = 11;

    public Symbol() {
    }

    /* CONSTRUCTORS */

    /** Class constructor specifying name and sort. As this is
     *  an abstract class this is strictly for use by subclasses.
     */
    protected Symbol(String name, Sort sort) {
        super(name);
        this.sort = sort;
    }

    /** Allows CoarseSymbolVisitor objects to visit this object.
     */
    public abstract Object apply(CoarseSymbolVisitor csv);

    /** Allows FineSymbolVisitor objects to visit this object.
     */
    public abstract Object apply(FineSymbolVisitor fsv);

    /* ACCESSORS */

    /** Gets the sort of this symbol.
     * @return Sort of this symbol.
     * @see Sort
     */
    public Sort getSort() {
        return this.sort;
    }

    /** Sets the sort of this symbol.
     * @param sort New sort for this symbol.
     * @see Sort
     */
    public void setSort(Sort sort) {
    this.sort = sort;
    }

    /* MISC. METHODS */

    /**
     * Compares the specified object with this symbol for equality. It
     * is equal to another Symbol, if the sort and the name match.
     *
     * @param o Symbol to be compared for equality with this symbol.
     * @return <code>true</code> if the specified symbol is equal to
     * this symbol, <code>false</code> otherwise.
     */
    @Override
    public boolean equals(Object o) {

    if (!(o instanceof Symbol)) {
        return false;
    }
    Symbol symbol = (Symbol) o;
    return this.name.equals(symbol.name);

    }

    /**
     * Returns an integer, representing the hash code value of this
     * <code>Symbol</code>. The hash code is the sum of the sort's
     * hash code and the hash code value generated from the name of
     * the symbol.
     *
     * @return hash code of this <code>Symbol</code>
     */
    @Override
    public int hashCode() {
        return this.name.hashCode();
    }

    public abstract  Symbol deepcopy();

    /** Determines the set of symbols this symbol depends on.
     * Bug: Not known to work for general TRS.
     * @return Set of Symbols this symbol depends on.
     */
    public Set dependsOn(Program prog) {
    HashSet open = new HashSet();
    HashSet closed = new HashSet();
    open.add(this);
    while (!open.isEmpty()) {
        Symbol sym = (Symbol)open.iterator().next();
        open.remove(sym);
        if (!((sym instanceof VariableSymbol) || closed.contains(sym))) {
        closed.add(sym);
        if (sym instanceof DefFunctionSymbol) {
                    Iterator i = ((DefFunctionSymbol)sym).getBody(prog).iterator();
                    while (i.hasNext()) {
            Rule r = (Rule)i.next();
            open.addAll(r.getLeft().getFunctionSymbols());
            open.addAll(r.getRight().getFunctionSymbols());
            }
        }
        }
    }
    return closed;
    }

    /* CHECKABLE */

    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        super.check(checked);
        if (this.sort == null) {
        throw new RuntimeException("sort must not be null");
        }
        this.sort.check(checked);
    }
    }

    /* Forbidden for security's and sanity's sake */
    @Override
    protected Object clone() {
    throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
    }

    /* Returns a shallow copy of this object, i.e. a symbol that uses the
     *  same name and sort (and body for DefFunctionSymbols).
     *  <p>
     *  Note: Changing any of the above will result in changes to the
     *  orginal symbol.
     *
    public abstract Symbol shallowcopy();

    /** Returns a deep copy of this object, i.e. a symbol whose sort
     *  (and body for DefFunctionSymbols) have been copied.
     *
    public abstract Symbol deepcopy();*/

    @Override
    public String toHTML() {
        return this.name;
    }

    @Override
    public String toLaTeX() {
        return "\\mathsf{"+ToLaTeXVisitor.escape(this.name)+"}";
    }

    public abstract int getSignatureClass();

}
