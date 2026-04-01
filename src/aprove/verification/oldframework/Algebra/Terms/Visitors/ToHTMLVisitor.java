package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a String.
 *
 * If you are looking for a term to html converter that has a little more
 * power (Arr, arr, arr) try the {@link CustomizedToHTMLVisitor}
 * @author Burak Emir
 * @version $Id$
 */
public class ToHTMLVisitor implements FineGrainedTermVisitor {

    public int lastFixity = SyntacticFunctionSymbol.NOTINFIX;
    final public boolean contract;


    public static String escape(String s) {
        StringBuilder temp = new StringBuilder();
        int level = 0;
        boolean strike = false;
        boolean underline = false;
        boolean highlight = false;
        if (s.startsWith("-") && s.endsWith("-") && s.length() > 2) {
            s = s.substring(1, s.length()-1);
            strike = true;
            temp.append("<s>");
        }
        if (s.startsWith("_") && s.endsWith("_") && s.length() > 2) {
            s = s.substring(1, s.length()-1);
            underline = true;
            temp.append("<u>");
        }
        if (s.startsWith("*") && s.endsWith("*") && s.length() > 2) {
            s = s.substring(1, s.length()-1);
            highlight = true;
            temp.append("<strong>");
        }
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);

            if(c == '_' && i==0){
                temp.append(c);;
                continue;
            }

            switch(c) {
            case '_':
                temp.append("<sub><font size=\"-1\">");
                level++;
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
            case ']':
                for (; level > 0; level--) {
                temp.append("</font></sub>");
                }
                temp.append(c);
                break;
            default:
                temp.append(c);
            }
        }
        for (; level > 0; level--) {
            temp.append("</font></sub>");
        }
        if (strike) {
            temp.append("</s>");
        }
        if (underline) {
            temp.append("</u>");
        }
        if (highlight) {
            temp.append("</strong>");
        }
        return temp.toString();
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return "<font color=\"#CC8888\"><i>"+ToHTMLVisitor.escape(v.getName())+"&nbsp;</i></font>";
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp d) {
        return this.caseFunctionApp("<font color=\"#000088\">",d);
    }

    @Override
    public Object caseConstructorApp(ConstructorApp c) {
        if (c.getSymbol() instanceof TupleSymbol) {
            return this.caseFunctionApp("<font color=\"#006666\">",c);
        } else {
            return this.caseFunctionApp("<font color=\"#666600\">",c);
        }
    }

    protected Object caseFunctionApp(String color, AlgebraFunctionApplication f) {
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
        res.append(" "+color+ToHTMLVisitor.escape(fsym.getName())+"</font> ");
        this.lastFixity = fsym.getFixity();// set again cause changes in recursive calls
        res.append(f.getArgument(1).apply(this));
        if (needsBraces) {
            res.append(")");
        }
    }
    else {
        res = new StringBuffer(color+ToHTMLVisitor.escape(fsym.getName())+"</font>");
        List<AlgebraTerm> args = f.getArguments();
        if(this.contract && fsym.getArity() == 1){
            int i = 1;
            AlgebraTerm t = args.get(0);
            while (t.getSymbol().equals(fsym)){
                i++;
                t = t.getArgument(0);
            }
            if (i > 1){
                res.append("<sup>" + color + i +"</font> </sup>");
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
    }
    return res.toString();
    }

    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {

        StringBuffer stringBuffer = new StringBuffer();

        MetaFunctionSymbol metaFunctionSymbol = (MetaFunctionSymbol)metaFunctionApplication.getSymbol();

        if(metaFunctionSymbol.isWaveFrontIn()) {
            stringBuffer.append("<font color=\"bb0000\">WF<sub>in</sub></font>(");
        }

        if(metaFunctionSymbol.isWaveFrontOut()) {
            stringBuffer.append("<font color=\"bb0000\">WF<sub>out</sub></font>(");
        }

        if(metaFunctionSymbol.isWaveHole()) {
            stringBuffer.append("<font color=\"bb0000\">WH</font>(");
        }

        List<AlgebraTerm> args = metaFunctionApplication.getArguments();
        Iterator<AlgebraTerm> iterator = args.iterator();

        while(iterator.hasNext()) {
            stringBuffer.append(iterator.next().apply(this));
            if(iterator.hasNext()){
                stringBuffer.append(",");
            }
        }

        stringBuffer.append(")");

        return stringBuffer.toString();
    }

    public ToHTMLVisitor(boolean contractUnaries){
        this.contract = contractUnaries;
    }

    public static String apply(AlgebraTerm t) {
        return ToHTMLVisitor.apply(t, true);
    }

    public static String apply(AlgebraTerm t, boolean contractUnaries) {
        return (String)t.apply(new ToHTMLVisitor(contractUnaries));
    }


}
