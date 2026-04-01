package aprove.input.Programs.xsrs;

import java.util.*;

import aprove.input.Generated.xsrs.node.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that implements the second pass of
 *  the AST conversion.
 *  <p>
 *  This pass picks up all the strings.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

class Pass2 extends Pass {

    @Override
    public void caseASimpleRule(ASimpleRule node) {
        AlgebraVariable x = AlgebraVariable.create(VariableSymbol.create("x", this.poly));
        AlgebraTerm left = this.buildFromList(((AWord)node.getLeft()).getIdi(), x);
        AlgebraTerm right = this.buildFromList(((AWord)node.getRight()).getIdi(), x);
        this.prog.addRule(Rule.create(left, right));
    }

    @Override
    public void caseACollapseRule(ACollapseRule node) {
        AlgebraVariable x = AlgebraVariable.create(VariableSymbol.create("x", this.poly));
        AlgebraTerm left = this.buildFromList(((AWord)node.getLeft()).getIdi(), x);
        AlgebraTerm right = x;
        this.prog.addRule(Rule.create(left, right));
    }

    private AlgebraTerm buildFromList(LinkedList ids, AlgebraTerm t) {
        for (int i = ids.size()-1; i >= 0; i--) {
            String name = this.chop(((AIdi)ids.get(i)).getId());
            SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
            if (f == null) {
                f = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
                f.addArgSort(this.poly);
                this.poly.addConstructorSymbol((ConstructorSymbol) f);
                try {
                    this.prog.addConstructorSymbol((ConstructorSymbol)f);
                } catch (ProgramException e) {}
            }
            List<AlgebraTerm> args = new Vector<AlgebraTerm>();
            args.add(t);
            t = AlgebraFunctionApplication.create(f, args);
        }
        return t;
    }

}
