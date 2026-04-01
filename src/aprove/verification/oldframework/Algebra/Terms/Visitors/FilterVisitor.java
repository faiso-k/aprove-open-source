package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;
import java.util.logging.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Filters a term according to the given mapping from function symbols
 * to filter parameters.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class FilterVisitor implements CoarseGrainedTermVisitor {

    public static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Terms.Visitors.FilterVisitor");

    protected Map map;
    protected boolean allowNullFilter; // a filter that is not set can not be applied
                                    // otherwise, null is equivalent to filter nothing away

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return v.shallowcopy();
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)f.getSymbol();

        // find filter parameter
        Integer filterparam = (Integer)this.map.get(fsym);
        if (filterparam == null) { // Don't filter
            if (!this.allowNullFilter) {
                return null;
            }
//            log.log(Level.FINEST, "Not filtering application of {0} to {1}.\n", new Object[] {fsym, f.getArguments()});
            Iterator i = f.getArguments().iterator();
            while (i.hasNext()) {
                Object arg = ((AlgebraTerm)i.next()).apply(this);
                if (arg == null) {
                    return null;
                }
                args.add((AlgebraTerm) arg);
            }
            return AlgebraFunctionApplication.create(fsym, args);
        } else {
            List<Sort> argsorts = new Vector<Sort>();
            int param = filterparam.intValue();
//            log.log(Level.FINEST, "Filtering application of {0} to {1}: {2}.\n", new Object[] {fsym, f.getArguments(), Integer.valueOf(param)});
            int arity = fsym.getArity();
            int numremove = (int)Math.pow(2, arity);
            if (param < numremove) { // remove some arguments
                for (int i = 0; i < arity; i++) {
                    if (param % 2 == 0) {
                        Object arg = f.getArgument(i).apply(this);
                        if (arg == null) {
                            return null;
                        }
                        args.add((AlgebraTerm) arg);
                        argsorts.add(fsym.getArgSort(i));
                    }
                    param = param / 2;
                }
        SyntacticFunctionSymbol originalSym = fsym;
                if (fsym instanceof TupleSymbol) {
                    fsym = TupleSymbol.create(fsym.getName(), argsorts, fsym.getSort(), ((TupleSymbol)fsym).getOrigin());
                } else if (fsym instanceof ConstructorSymbol) {
                    fsym = ConstructorSymbol.create(fsym.getName(), argsorts, fsym.getSort());
                } else {
                    fsym = DefFunctionSymbol.create(fsym.getName(), argsorts, fsym.getSort());
                }
        if ((originalSym.getFixity()==SyntacticFunctionSymbol.INFIX || originalSym.getFixity()==SyntacticFunctionSymbol.INFIXL || originalSym.getFixity()==SyntacticFunctionSymbol.INFIXR) && argsorts.size()==2) {
            // INFIX
            fsym.setFixity(originalSym.getFixity(), originalSym.getFixityLevel());
        }
                return AlgebraFunctionApplication.create(fsym, args);
            } else { // filter to a certain argument
                return f.getArgument(param - numremove).apply(this);
            }
        }
    }

    public FilterVisitor(Map map) {
        this(map,true);
    }

    public FilterVisitor(Map map, boolean allowNullFilter) {
        this.map = map;
        this.allowNullFilter = allowNullFilter;
    }

}
