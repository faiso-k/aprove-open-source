package aprove.input.Programs.srs;

import java.util.*;

import aprove.input.Generated.srs.node.*;
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
    public void caseARule(ARule node) {
        AlgebraVariable x = AlgebraVariable.create(VariableSymbol.create("x", this.poly));
        AlgebraTerm left = this.buildFromList(node.getLeft(), x);
        AlgebraTerm right = this.buildFromList(node.getRight(), x);
        this.prog.addRule(Rule.create(left, right));
    }

    private AlgebraTerm buildFromList(Token id, AlgebraTerm t) {
        String names = this.chop(id);
        for (int i = names.length()-1; i >= 0; i--) {
            String name = ""+names.charAt(i);
            SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
            if (f == null) {
                f = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
                f.addArgSort(this.poly);
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
