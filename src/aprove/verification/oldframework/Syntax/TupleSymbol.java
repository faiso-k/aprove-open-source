package aprove.verification.oldframework.Syntax;

import java.util.*;

/** A tuple symbol is a special function symbol.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class TupleSymbol extends ConstructorSymbol {

    /** The defined function symbol this tuplesymbol was created from.*/
    protected DefFunctionSymbol origin;
    private List<Sort> argsorts;

    /* constructors */

    protected TupleSymbol(String name, List<Sort> argsorts, Sort sort, DefFunctionSymbol origin) {
        super(name, argsorts, sort);
        this.argsorts = argsorts;
        this.origin = origin;
    }

    protected TupleSymbol(String name, int arity, DefFunctionSymbol origin) {
        super(name,arity);
        this.origin = origin;
    }

    public static TupleSymbol create(String name, List<Sort> argsorts, Sort sort, DefFunctionSymbol origin) {
    return new TupleSymbol(name, argsorts, sort, origin);
    }

    public static TupleSymbol create(String name, int arity, DefFunctionSymbol origin) {
        return new TupleSymbol(name,arity,origin);
    }

    /* access methods */

    public DefFunctionSymbol getOrigin() {
        return this.origin;
    }

    @Override
    public List<Sort> getArgSorts() {
        return this.argsorts;
    }

    /* misc methods */

    @Override
    public boolean equals(Object o) {
        if (o instanceof TupleSymbol) {
            TupleSymbol symbol = (TupleSymbol)o;
            return this.name.equals(symbol.name) && this.origin.equals(symbol.origin);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return super.toString()+" [<"+this.origin.getName()+">]";
    }

    @Override
    public String verboseToString() {
    StringBuffer temp = new StringBuffer("{tuple "+this.name+" [<"+this.origin.getName()+">] ::");
    for (Iterator i = this.argsorts.iterator(); i.hasNext();) {
        temp.append(((Sort)i.next()).getName());
        if (i.hasNext()) {temp.append(", ");} else {temp.append(" -> ");}
    }
    return temp.toString()+"}\n";
    }

    @Override
    public Symbol shallowcopy() {
    TupleSymbol res = new TupleSymbol(this.name, this.argsorts, this.sort, this.origin);
        res.setFixity(this.getFixity(), this.getFixityLevel());
        return res;
    }

    @Override
    public Symbol deepcopy() {
    Vector<Sort> v = new Vector<Sort>();
    Iterator i = this.argsorts.iterator();
    while (i.hasNext()) {
        v.add((Sort)i.next());
    }
    TupleSymbol res = new TupleSymbol(this.name, v, this.sort, this.origin);
        res.setFixity(this.getFixity(), this.getFixityLevel());
        return res;
    }

}
