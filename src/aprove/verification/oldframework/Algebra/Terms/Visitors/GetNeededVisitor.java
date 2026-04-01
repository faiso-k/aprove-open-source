package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;
import java.util.logging.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Filters a term according to the given mapping from function symbols
 * to filter parameters and determine the function symbols used in the process.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class GetNeededVisitor implements CoarseGrainedTermVisitor {

    public static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Terms.Visitors.GetNeededVisitor");

    protected Map map;
    protected Set<SyntacticFunctionSymbol> needed;

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return null;
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)f.getSymbol();
        int arity = fsym.getArity();
        if (arity == 0) {
            return null;
        }
        this.needed.add(fsym);
        // find filter parameter
        Integer filterparam = (Integer)this.map.get(fsym);
        if (filterparam == null) { // Don't filter
            Iterator i = f.getArguments().iterator();
            while (i.hasNext()) {
                AlgebraTerm arg = (AlgebraTerm)i.next();
                arg.apply(this);
            }
        } else {
            int param = filterparam.intValue();
            int numremove = (int)Math.pow(2, arity);
            if (param < numremove) { // remove some arguments
                for (int i = 0; i < arity; i++) {
                    if (param % 2 == 0) {
                        f.getArgument(i).apply(this);
                    }
                    param = param / 2;
                }
            } else { // filter to a certain argument
                f.getArgument(param - numremove).apply(this);
            }
        }
        return null;
    }

    public Set<SyntacticFunctionSymbol> getNeeded() {
        return this.needed;
    }

    public GetNeededVisitor(Map map) {
        this.map = map;
        this.needed = new LinkedHashSet<SyntacticFunctionSymbol>();
    }

}
