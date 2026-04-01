package aprove.input.Terms.term;

import aprove.input.Generated.term.node.*;
import aprove.input.Generated.term.parser.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that implements a transformation pass.
 *  <p>
 *  The AST get's transformed according to rules that
 *  result from left/right-associativity of operators.
 *  </p>
 *  @author Christian Haselbach
 *  @version $Id$
 */

class TransformPass extends Pass {

    /** Rearrange the tree if the right term has an operator with
     *  a lower precedence then the current symbol as a root-symbol.
     */
    @Override
    public void caseAInfixTerm(AInfixTerm node) {
        TInfixId id = node.getInfixId();
    TInfixId id2 = null;
    String op = this.chop(id);
        PNterm leftnode = node.getLeft();
        PTerm rightnode = node.getRight();
    boolean rearrange = false;
    if (rightnode instanceof AInfixTerm) {
        id2 = ((AInfixTerm)rightnode).getInfixId();
        String op2 = this.chop(id2);
        int level1;
        int fixity;
        SyntacticFunctionSymbol fsym = this.prog.getFunctionSymbol(op);
        if (fsym == null) {
            fsym = this.prog.getPredefFunctionSymbol(op);
        }
        if (fsym == null) {
        level1 = 9;
        fixity = SyntacticFunctionSymbol.INFIXR;
        }
        else {
        level1 = fsym.getFixityLevel();
        fixity = fsym.getFixity();
        }
        int level2;
        fsym = this.prog.getFunctionSymbol(op2);
        if (fsym == null) {
            fsym = this.prog.getPredefFunctionSymbol(op2);
        }
        if (fsym == null) {
        level2 = 9;
        }
        else {
        level2 = fsym.getFixityLevel();
        }
        if (level1 > level2 || (op.equals(op2) && fixity == SyntacticFunctionSymbol.INFIXL)) {
        rearrange = true;
        }
        else if (op.equals(op2) && fixity == SyntacticFunctionSymbol.INFIX) {
        this.errors.add(new ParserException(node.getInfixId(), "Ambiguous use of operator ''"+op+"''"));
        }
    }
        if (rearrange) {
        PNterm r_left = ((AInfixTerm)rightnode).getLeft();
        PTerm r_right = ((AInfixTerm)rightnode).getRight();
        AParenNterm newleft = new AParenNterm(new TOpen(), new AInfixTerm(leftnode, id, new ANormalTerm(r_left)), new TClose());
        node.setInfixId(id2);
        node.setLeft(newleft);
        node.setRight(r_right);
        node.apply(this);
        }
    else {
        leftnode.apply(this);
        rightnode.apply(this);
    }
    }

}

