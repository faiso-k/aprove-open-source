package aprove.verification.oldframework.Syntax;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;

/** A constructor symbol is a special function symbol.
 * @author Peter Schneider-Kamp, Eugen Yu
 * @version $Id$
 */

public class ConstructorSymbol extends SyntacticFunctionSymbol {

    protected Vector<DefFunctionSymbol> selectors = null;
    protected DefFunctionSymbol isa = null;

    /* constructors */

    protected ConstructorSymbol(String name, List<Sort> argsorts, Sort sort) {
    super(name, argsorts, sort);
    }

    protected ConstructorSymbol(String name, int arity) {
        super(name,arity);
    }

    public static ConstructorSymbol create(String name, List<Sort> argsorts, Sort sort) {
        return new ConstructorSymbol(name, argsorts, sort);
    }

    public static ConstructorSymbol create(String name,int arity, Sort sort) {
        return new ConstructorSymbol(name, Sort.getVectorOfStandardSort(arity,sort),sort);
    }

    public static ConstructorSymbol create(String name, int arity) {
        return new ConstructorSymbol(name,arity);
    }

    public static ConstructorSymbol create(String name, int arity, int fixity) {
        ConstructorSymbol constructorSymbol = new ConstructorSymbol(name,arity);
        constructorSymbol.setFixity(fixity);
        return constructorSymbol;
    }

    public static ConstructorSymbol create(String name, int arity, Sort sort, int fixity, int fixityLevel) {
    ConstructorSymbol forReturn = ConstructorSymbol.create(name, arity, sort);
    forReturn.setFixity(fixity);
    forReturn.setFixityLevel(fixityLevel);
    return forReturn;
    };

    /** Allows FineSymbolVisitor objects to visit this object.
     */
    @Override
    public Object apply(FineSymbolVisitor fsv) {
    return fsv.caseConstructorSymbol(this);
    }

    /* misc methods */

    public boolean isReflexive() {
    boolean reflexive = false;
    for (int i=0; i<this.argSorts.size(); i++) {
        reflexive = reflexive || (this.getArgSort(i) == this.getSort());
    }
    return reflexive;
    }

    @Override
    public String toString() {
        return super.toString();
    }

    public String toString(Program prog) {
    StringBuffer temp = new StringBuffer(super.toString()+" [\n");
    for (Iterator i = prog.getEquations(this).iterator(); i.hasNext();) {
        temp.append("  "+((TRSEquation)i.next()).toString());
        temp.append("\n");
    }
    temp.append("]\n");
    return temp.toString();
    }

    @Override
    public String verboseToString() {
    StringBuffer temp = new StringBuffer("{cons "+this.name+"::");
    for (Iterator i = this.argSorts.iterator(); i.hasNext();) {
        temp.append(((Sort)i.next()).getName());
        if (i.hasNext()) {temp.append(", ");} else {temp.append(" -> ");}
    }
    return temp.toString()+"}\n";
    }

    /** Get all argument positions where its sort is equal to the sort of this constructor.
     */

    public Set<Position> getReflexivePositions() {
    Set<Position> result = new HashSet<Position>();
    for (int i=0; i<this.argSorts.size(); i++) {
        Sort s = this.argSorts.get(i);
        if (s.equals(this.getSort())) {
        Position pos = Position.create();
        pos.add(i);
        result.add(pos);
        }
    }
    return result;
    }

    public boolean isReflexivePosition(int position) {
        return this.sort.equals(this.argSorts.get(position));
    }

    public Symbol shallowcopy() {
    ConstructorSymbol res = new ConstructorSymbol(this.name, this.argSorts, this.sort);
        res.setFixity(this.getFixity(), this.getFixityLevel());
        return res;
    }

    @Override
    public Symbol deepcopy() {
    Vector<Sort> v = new Vector<Sort>();
    Iterator i = this.argSorts.iterator();
    while (i.hasNext()) {
        v.add((Sort)i.next());
    }
    ConstructorSymbol res = new ConstructorSymbol(this.name, v, this.sort);
        res.setFixity(this.getFixity(), this.getFixityLevel());
        return res;
    }

    @Override
    public int getSignatureClass() {
    return Symbol.CONSSIG;
    }

    public void setSelectors(Vector<DefFunctionSymbol> sels) {
    this.selectors = sels;
    }

    public Vector<DefFunctionSymbol> getSelectors() {
    return this.selectors;
    }

    public void setIsa(DefFunctionSymbol fIsa) {
    this.isa = fIsa;
    }

    public DefFunctionSymbol getIsa() {
    return this.isa;
    }

}
