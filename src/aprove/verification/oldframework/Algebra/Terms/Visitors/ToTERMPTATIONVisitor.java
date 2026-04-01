package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/** Converts a Term into a String.
 * @author Burak Emir
 * @version $Id$
 */
public class ToTERMPTATIONVisitor implements CoarseGrainedTermVisitor {

    FreshNameGenerator vars, funcs;

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return this.vars.getFreshName(v.getName(), true);
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        List<AlgebraTerm> args = f.getArguments();
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
        StringBuffer res = new StringBuffer(this.funcs.getFreshName(fsym.getName(), true));
        if (fsym.getArity() > 0) {
            res.append("(");
            Iterator i = args.iterator();
            while (i.hasNext()) {
                // apply this visitor to arguments
                AlgebraTerm t =  (AlgebraTerm)i.next();
                String temp = (String)t.apply(this);
                res.append(temp);
                if (i.hasNext()) {
                    res.append(", ");
                }
            }
            res.append(")");
        }
        return res.toString();
    }

    public ToTERMPTATIONVisitor(FreshNameGenerator vars, FreshNameGenerator funcs) {
        super();
        this.vars = vars;
        this.funcs = funcs;
    }

    public static String apply(AlgebraTerm t, FreshNameGenerator vars, FreshNameGenerator funcs) {
        return (String)t.apply(new ToTERMPTATIONVisitor(vars, funcs));
    }

}
