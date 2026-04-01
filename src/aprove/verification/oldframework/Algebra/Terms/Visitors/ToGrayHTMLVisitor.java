package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */
public class ToGrayHTMLVisitor implements CoarseGrainedTermVisitor {

    public int lastFixity = SyntacticFunctionSymbol.NOTINFIX;

    public static String escape(String s) {
        StringBuffer temp = new StringBuffer();
        int level = 0;
        boolean strike = false;
        boolean underline = false;
        boolean highlight = false;
        if (s.startsWith("-") && s.endsWith("-") && s.length() > 2) {
            s = s.substring(1, s.length()-1);
            strike = true;
            temp.append("<S>");
        }
        if (s.startsWith("_") && s.endsWith("_") && s.length() > 2) {
            s = s.substring(1, s.length()-1);
            underline = true;
            temp.append("<U>");
        }
        if (s.startsWith("*") && s.endsWith("*") && s.length() > 2) {
            s = s.substring(1, s.length()-1);
            highlight = true;
            temp.append("<STRONG>");
        }
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch(c) {
                case '_':
                    temp.append("<SUB><FONT SIZE=\"-1\">");
                    level++;
                    break;
                case '[':
                    temp.append("{");
                    break;
                case ']':
                    for (; level > 0; level--) {
                        temp.append("</FONT></SUB>");
                    }
                    temp.append("}");
                    break;
                case '>':
                    temp.append("&gt;");
                    if (i == s.length()-1) {
                        temp.append("&nbsp;");
                    }
                    break;
                case '<':
                    temp.append("&lt;");
                    if (i == s.length()-1) {
                        temp.append("&nbsp;");
                    }
                    break;
                case '&':
                    temp.append("&amp;");
                    if (i == s.length()-1) {
                        temp.append("&nbsp;");
                    }
                    break;
                case ',':
                    for (; level > 0; level--) {
                        temp.append("</FONT></SUB>");
                    }
                    temp.append(c);
                    break;
                default:
                    temp.append(c);
            }
        }
        for (; level > 0; level--) {
            temp.append("</FONT></SUB>");
        }
        if (strike) {
            temp.append("</S>");
        }
        if (underline) {
            temp.append("</U>");
        }
        if (highlight) {
            temp.append("</STRONG>");
        }
        return temp.toString();
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return "<I>"+ToGrayHTMLVisitor.escape(v.getName())+"</I>";
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
            res.append(" "+ToGrayHTMLVisitor.escape(fsym.getName()));
            this.lastFixity = fsym.getFixity();// set again cause changes in recursive calls
            res.append(f.getArgument(1).apply(this));
            if (needsBraces) {
                res.append(")");
            }
        }
        else {
            res = new StringBuffer(ToGrayHTMLVisitor.escape(fsym.getName()));
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

    public static String apply(AlgebraTerm t) {
        return "<FONT COLOR=#cecece>" + (String)t.apply(new ToGrayHTMLVisitor()) + "</FONT>";
    }

}
