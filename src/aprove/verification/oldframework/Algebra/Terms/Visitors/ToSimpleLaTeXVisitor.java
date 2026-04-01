package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a String.
 * @author Achim Luecking, Burak Emir
 * @version $Id$
 */
public class ToSimpleLaTeXVisitor implements FineGrainedTermVisitor {

    public int lastFixity = SyntacticFunctionSymbol.NOTINFIX;

    public static String escape(String s) {
        StringBuffer temp = new StringBuffer();
        int level = 0;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch(c) {
            case '0':
                temp.append("z");
                break;
            case '_':
                temp.append("under");
                break;
            /*case '[':
                temp.append("\\left\\{");
                break;
            case ']':
                for (; level > 0; level--) {
                    temp.append("}");
                }
                temp.append("\\right\\}");
                break;
            case ',':
                for (; level > 0; level--) {
                    temp.append("}");
                }
                temp.append(c);
                break;*/
            case '@':
                temp.append("at");
                break;
            case '|':
                temp.append("pipe");
                break;
            case '/':
                temp.append("div");
                break;
            case '\\':
                temp.append("vid");
                break;
            case ':':
                temp.append("col");
                break;
            case '-':
                temp.append("minus");
                break;
            case '+':
                temp.append("plus");
                break;
            case '*':
                temp.append("times");
                break;
            case '.':
                temp.append("dot");
                break;
            case '<':
                temp.append("less");
                break;
            case '>':
                temp.append("more");
                break;
            case '=':
                temp.append("equal");
                break;
            case '!':
                temp.append("bang");
                break;
            case '$':
                temp.append("bucks");
                break;
            case '?':
                temp.append("what");
                break;
            case '&':
                temp.append("and");
                break;
            case '%':
                temp.append("percent");
                break;
            case '#':
                temp.append("pigfence");
                break;
            case '^':
                temp.append("hat");
                break;
            default:
                temp.append(c);
                break;
            }
        }
        for (; level > 0; level--) {
            temp.append("}");
        }
        return temp.toString();
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return ToSimpleLaTeXVisitor.escape(v.getName());
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp d) {
        return this.caseFunctionApp(d);
    }

    @Override
    public Object caseConstructorApp(ConstructorApp c) {
        if (c.getSymbol() instanceof TupleSymbol) {
            return this.caseFunctionApp(c);
        } else {
            return this.caseFunctionApp(c);
        }
    }

    private Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
    StringBuffer res;
    if (fsym.isInfix()) {
        boolean needsBraces = this.lastFixity != SyntacticFunctionSymbol.NOTINFIX;
        res = new StringBuffer();
        if (needsBraces) {
            res.append("(");
        }
        this.lastFixity = fsym.getFixity();
        res.append((String)f.getArgument(0).apply(this));
        res.append(" \\AProVEf"+ToSimpleLaTeXVisitor.escape(fsym.getName()) + " ");
        //        res.append(" \\mathsf{"+escape(fsym.getName())+"} ");
        this.lastFixity = fsym.getFixity();// set again cause changes in recursive calls
        res.append((String)f.getArgument(1).apply(this));
        if (needsBraces) {
            res.append(")");
        }
    }
    else {
        res = new StringBuffer("\\AProVEf"+ToSimpleLaTeXVisitor.escape(fsym.getName()));
        List<AlgebraTerm> args = f.getArguments();
        if (fsym.getArity() > 0) {
        res.append("(");
        Iterator i = args.iterator();
        while (i.hasNext()) {
            // apply this visitor to arguments
            AlgebraTerm t =  (AlgebraTerm)i.next();
            this.lastFixity = SyntacticFunctionSymbol.NOTINFIX;
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
        return (String)t.apply(new ToSimpleLaTeXVisitor());
    }

}
