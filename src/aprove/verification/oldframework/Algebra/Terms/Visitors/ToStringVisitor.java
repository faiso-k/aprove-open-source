package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a String.
 * @author Burak Emir
 * @version $Id$
 */
public class ToStringVisitor implements CoarseGrainedTermVisitor {

    public int lastFixity = SyntacticFunctionSymbol.NOTINFIX;
    final public boolean contract;

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return v.getName();
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
    StringBuffer res;
    if (fsym.isInfix()) {
        boolean needsBraces = this.lastFixity != SyntacticFunctionSymbol.NOTINFIX;
        this.lastFixity = fsym.getFixity();
        res = new StringBuffer();
        if (needsBraces) {
            res.append("(");
        }
        res.append((String)f.getArgument(0).apply(this));
        res.append(" "+fsym.getName()+" ");
        this.lastFixity = fsym.getFixity();
        res.append((String)f.getArgument(1).apply(this));
        if (needsBraces) {
            res.append(")");
        }
    }
    else {
        List<AlgebraTerm> args = f.getArguments();
        res = new StringBuffer(fsym.getName());
        if(this.contract && fsym.getArity() == 1){
            int i = 1;
            AlgebraTerm t = args.get(0);
            while (t.getSymbol().equals(fsym)){
                i++;
                t = t.getArgument(0);
            }
            if (i > 1){
                res.append("^" + i);
            }
            res.append("(");
            this.lastFixity = SyntacticFunctionSymbol.NOTINFIX;
            String temp = (String) t.apply(this);
            res.append(temp);
            res.append(")");
        }
        else{
            if (fsym.getArity() > 0) {
                res.append("(");
                Iterator i = args.iterator();
                while (i.hasNext()) {
                    // apply this visitor to arguments
                    this.lastFixity = SyntacticFunctionSymbol.NOTINFIX;
                    AlgebraTerm t =  (AlgebraTerm)i.next();
                    String temp = (String)t.apply(this);
                    res.append(temp);
                    if (i.hasNext()) {
                        res.append(", ");
                    }
                }
                res.append(")");
            }
        }
    }
        return res.toString();
    }

    public ToStringVisitor(boolean contractUnaries){
        this.contract = contractUnaries;
    }

    public static String apply(AlgebraTerm t) {
        return ToStringVisitor.apply(t, true);
    }

    public static String apply(AlgebraTerm t, boolean contractUnaries) {
        return (String)t.apply(new ToStringVisitor(contractUnaries));
    }

}
