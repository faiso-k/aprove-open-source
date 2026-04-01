package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a HTML-string where a givne position is highlighted.
 * @author Burak Emir, Christian Haselbach
 * @version $Id$
 */
public class HighlightTermVisitor implements CoarseGrainedTermVisitor {

    protected Position hlPos;
    protected Position curPos;
    protected boolean useHTML;

    protected HighlightTermVisitor(Position p, boolean useHTML) {
    this.hlPos = p;
    this.curPos = Position.create();
    this.useHTML = useHTML;
    }

    public int lastFixity = SyntacticFunctionSymbol.NOTINFIX;

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return v.getName();
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
    String name = ToHTMLVisitor.escape(fsym.getName());
    Position localPos = this.curPos;
    StringBuffer res;
    if (fsym.isInfix()) {
        boolean needsBraces = this.lastFixity != SyntacticFunctionSymbol.NOTINFIX;
        this.lastFixity = fsym.getFixity();
        res = new StringBuffer();
        if (needsBraces) {
            res.append("(");
        }
        this.curPos = localPos.shallowcopy();
        this.curPos.add(0);
        res.append((String)f.getArgument(0).apply(this));
        if (localPos.equals(this.hlPos)) {
        res.append(" <FONT COLOR=\"RED\">"+name+"</FONT> ");
            }
        else {
        res.append(" "+name+" ");
            }
        this.curPos = localPos.shallowcopy();
        this.curPos.add(1);
        res.append((String)f.getArgument(1).apply(this));
        if (needsBraces) {
            res.append(")");
        }
    }
    else {
        List<AlgebraTerm> args = f.getArguments();
        if (localPos.equals(this.hlPos)) {
        res = new StringBuffer("<FONT COLOR=\"RED\">"+name+"</FONT>");
        }
        else {
        res = new StringBuffer(fsym.getName());
        }
        if (fsym.getArity() > 0) {
        res.append("(");
        Iterator it = args.iterator();
        for (int i=0; it.hasNext(); i++) {
            // apply this visitor to arguments
            AlgebraTerm t =  (AlgebraTerm)it.next();
            this.curPos = localPos.shallowcopy();
            this.curPos.add(i);
            this.lastFixity = SyntacticFunctionSymbol.NOTINFIX;
            String temp = (String)t.apply(this);
            res.append(temp);
            if (it.hasNext()) {
            res.append(", ");
            }
        }
        res.append(")");
        }
    }
        return res.toString();
    }

    public static String apply(AlgebraTerm t, Position p, boolean useHTML) {
        return (String)t.apply(new HighlightTermVisitor(p, useHTML));
    }

}
