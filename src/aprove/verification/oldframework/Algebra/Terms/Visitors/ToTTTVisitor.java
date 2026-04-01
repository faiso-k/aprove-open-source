package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a String.
 * @author Burak Emir
 * @version $Id$
 */
public class ToTTTVisitor implements FineGrainedTermVisitor {

    public int lastFixity = SyntacticFunctionSymbol.NOTINFIX;

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return v.getName();
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp d) {
        return this.caseFunctionApp(d);
    }

    @Override
    public Object caseConstructorApp(ConstructorApp c) {
        return this.caseFunctionApp(c);
    }

    private boolean numeric(String s) {
        for (int i = 0; i < s.length(); i++) {
            if (Character.getType(s.charAt(i)) != Character.DECIMAL_DIGIT_NUMBER) {
                return false;
            }
        }
        return true;
    }

    private Object caseFunctionApp(AlgebraFunctionApplication f) {
        List<AlgebraTerm> args = f.getArguments();
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
        StringBuffer res = new StringBuffer(fsym.getName());
        if (!this.numeric(fsym.getName())) {
        if (fsym.isInfix()) {
            boolean needsBraces = this.lastFixity != SyntacticFunctionSymbol.NOTINFIX;
            res = new StringBuffer();
            if (needsBraces) {
                res.append("(");
            }
            this.lastFixity = fsym.getFixity();
            res.append((String)f.getArgument(0).apply(this));
            res.append(" "+fsym.getName()+" ");
            this.lastFixity = fsym.getFixity();// set again cause changes in recursive calls
            res.append((String)f.getArgument(1).apply(this));
            if (needsBraces) {
                res.append(")");
            }
        }
        else {
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
        }
        return res.toString();
    }

    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return null;
    }

    public static String apply(AlgebraTerm t) {
        return (String)t.apply(new ToTTTVisitor());
    }

}
