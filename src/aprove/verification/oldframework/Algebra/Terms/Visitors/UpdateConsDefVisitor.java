package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Updates which symbols are constructors and which are defined
 * function symbols.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class UpdateConsDefVisitor implements CoarseGrainedTermVisitor {

    protected Map<String,SyntacticFunctionSymbol> toCons;
    protected Map<String,SyntacticFunctionSymbol> toDef;

    public UpdateConsDefVisitor(Set<SyntacticFunctionSymbol> toCons, Set<SyntacticFunctionSymbol> toDef) {

    this.toDef = new HashMap<String,SyntacticFunctionSymbol>();
    Iterator defIter = toDef.iterator();
    while (defIter.hasNext()) {
        SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol) defIter.next();
        this.toDef.put(sym.getName(), sym);
    }

    this.toCons = new HashMap<String,SyntacticFunctionSymbol>();
    Iterator consIter = toCons.iterator();
    while (consIter.hasNext()) {
        SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol) consIter.next();

        // DefFunctionSymbols get priority

        if (!this.toDef.containsKey(sym.getName())) {
        this.toCons.put(sym.getName(), sym);
        }
    }

    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
    return v.deepcopy();
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
    Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
        Vector<Sort> vs = new Vector<Sort>();
        for (int i = 0; i < f.getArguments().size(); i++) {
            AlgebraTerm arg = (AlgebraTerm)f.getArgument(i).apply(this);
            v.add(arg);
            vs.add(arg.getSort());
        }
        SyntacticFunctionSymbol fsym = f.getFunctionSymbol();
        if (fsym instanceof TupleSymbol) {
        fsym = TupleSymbol.create(fsym.getName(), fsym.getArgSorts(), fsym.getSort(), ((TupleSymbol) fsym).getOrigin());
        } else if (this.toCons.containsKey(fsym.getName())) {
            fsym = ConstructorSymbol.create(fsym.getName(), vs, fsym.getSort());
        } else if (this.toDef.containsKey(fsym.getName())) {
            // by copying first, derivations of DefFunctionSymbols will be preserved (when they overload deepcopy properly)
            fsym = (SyntacticFunctionSymbol)this.toDef.get(fsym.getName()).deepcopy();

            // if the symbol in the mapping is not already a DefFunctionSymbol, create a new one
            if (!(fsym instanceof DefFunctionSymbol)) {
                fsym = DefFunctionSymbol.create(fsym.getName(), vs, fsym.getSort());
            }
        } else if (fsym instanceof ConstructorSymbol) {
            fsym = ConstructorSymbol.create(fsym.getName(), vs, fsym.getSort());
        } else if (fsym instanceof DefFunctionSymbol) {
            // it is not contained in the mapping, so simply copy it (again, to preserve derivations)
            fsym = (SyntacticFunctionSymbol)fsym.deepcopy();
    }
        fsym.setFixity(f.getFunctionSymbol().getFixity(), f.getFunctionSymbol().getFixityLevel());
    AlgebraTerm t = AlgebraFunctionApplication.create(fsym, v);
    t.setAttributes(f.getAttributes());
    return t;
    }

    public static AlgebraTerm apply(AlgebraTerm t, Set<SyntacticFunctionSymbol> toCons, Set<SyntacticFunctionSymbol> toDef) {
    return (AlgebraTerm)t.apply(new UpdateConsDefVisitor(toCons, toDef));
    }

}
