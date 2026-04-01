package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into XML.
 * @author Barbara Friemann
 * @version $Id$
 */
public class ToXMLVisitor implements FineGrainedTermVisitor {

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return "<Term><Varsym sort=\"" + v.getSort().toString() + "\">"+ v.getName().toString() + "</Varsym></Term>";
    }
    public static String apply(AlgebraTerm t) {
        return (String)t.apply(new ToXMLVisitor());
    }

    @Override
    public Object caseConstructorApp(ConstructorApp cterm) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)cterm.getSymbol();
        StringBuffer res = new StringBuffer();
        res.append("<Term>");
        if (fsym.isInfix()) {
            res.append("<Conssym infix=\"yes\" sort=\"" + cterm.getSort() + "\">");
        } else {
            res.append("<Conssym infix=\"no\" sort=\"" + cterm.getSort() + "\">");
        }
        res.append(cterm.getSymbol().getName() + "</Conssym>");
        List<AlgebraTerm> args = cterm.getArguments();
        if (fsym.getArity() > 0) {
            Iterator i = args.iterator();
            while (i.hasNext()) {
                // apply this visitor to arguments
                AlgebraTerm t =  (AlgebraTerm)i.next();
                String temp = (String)t.apply(this);
                res.append(temp);
            }
        }
        res.append("</Term>");
        return res.toString();
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp fterm) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)fterm.getSymbol();
        StringBuffer res = new StringBuffer();
        res.append("<Term>");
        if (fsym.isInfix()) {
            res.append("<Defsym infix=\"yes\" sort=\"" + fterm.getSort() + "\">");
        } else {
            res.append("<Defsym infix=\"no\" sort=\"" + fterm.getSort() + "\">");
        }
        res.append(fterm.getSymbol().getName() + "</Defsym>");
        List<AlgebraTerm> args = fterm.getArguments();
        if (fsym.getArity() > 0) {
            Iterator i = args.iterator();
            while (i.hasNext()) {
                // apply this visitor to arguments
                AlgebraTerm t =  (AlgebraTerm)i.next();
                String temp = (String)t.apply(this);
                res.append(temp);
            }
        }
        res.append("</Term>");
        return res.toString();
    }

    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return null;
    }


}
