package aprove.input.Programs.fp;

import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Treewalker that implements a transformation pass.
 *  <p>
 *  The AST get's transformed according to rules that
 *  result from left/right-associativity of operators.
 *  </p>
 *  @author Christian Haselbach
 *  @version $Id$
 */

class TransformPass extends Pass {

    private Stack<Boolean> hasChanged = new Stack<Boolean>();

    /** Rearrange the tree if the right term has an operator with
     *  a lower precedence then the current symbol as a root-symbol.
     */
    @Override
    public void caseAOperatorTerm(AOperatorTerm node) {
        TInfixid id = node.getInfixid();
    String op = this.chop(id);
        PTterm leftnode = node.getLeft();
        PTerm rightnode = node.getRight();
    boolean rearrange = false;
    if (rightnode instanceof AOperatorTerm) {
        TInfixid id2 = ((AOperatorTerm)rightnode).getInfixid();
        String op2 = this.chop(id2);
        int level1;
        int fixity;
        if (op.equals("==")) {
            Pair<Integer,Integer> fixityAndPrecedence = this.operatorFixity.get("==");
            if (fixityAndPrecedence != null) {
                fixity = fixityAndPrecedence.x;
                level1 = fixityAndPrecedence.y;
            }
            else {
                fixity = SyntacticFunctionSymbol.INFIX;
                level1 = 4;
            }
        }
        else {
            Pair<Integer,Integer> fixityAndPrecedence = this.operatorFixity.get(op);

            if (fixityAndPrecedence == null) {
                level1 = 9;
                fixity = SyntacticFunctionSymbol.INFIXR;
            }
            else {
                fixity = fixityAndPrecedence.x;
                level1 = fixityAndPrecedence.y;
            }
        }
        int level2;
        if (op2.equals("==")) {
            Pair<Integer,Integer> fixityAndPrecedence = this.operatorFixity.get("==");
            if (fixityAndPrecedence != null) {
                level2 = fixityAndPrecedence.y;
            }
            else {
                level2 = 4;
            }
        }
        else {
            Pair<Integer,Integer> fixityAndPrecedence = this.operatorFixity.get(op2);

            if (fixityAndPrecedence == null) {
                level2 = 9;
            }
            else {
                level2 = fixityAndPrecedence.y;
            }
        }
        if (level1 > level2 || ( (op.equals(op2) || (level1 == level2)) && fixity == SyntacticFunctionSymbol.INFIXL) ) {
            rearrange = true;
            if ( (this.hasChanged.size() > 0) && (!this.hasChanged.peek()) ) {
                this.hasChanged.pop();
                this.hasChanged.push(true);
            }
        }
        else if (op.equals(op2) && fixity == SyntacticFunctionSymbol.INFIX) {
        this.addParseError(node.getInfixid(), "Ambiguous use of operator ''"+op+"''");
        }
    }
        if (rearrange) {
            PTterm leftnode2 = ((AOperatorTerm)rightnode).getLeft();
            PTerm rightnode2 = ((AOperatorTerm)rightnode).getRight();
            TInfixid id2 = ((AOperatorTerm)rightnode).getInfixid();
            ((AOperatorTerm)rightnode).setInfixid(id);
            node.setInfixid(id2);
            ((AOperatorTerm)rightnode).setLeft((PTterm)leftnode);
            ATtermSterm tmpnode1 = new ATtermSterm();
            tmpnode1.setTterm((PTterm)leftnode2);
            AStermTerm tmpnode2 = new AStermTerm();
            tmpnode2.setSterm((PSterm)tmpnode1);
            ((AOperatorTerm)rightnode).setRight((PTerm)tmpnode2);
        AParTterm tmpnode3 = new AParTterm();
        tmpnode3.setTerm((PTerm)rightnode);
        node.setLeft((PTterm)tmpnode3);
        node.setRight(rightnode2);
        node.apply(this);
        }
    else {
        this.hasChanged.push(false);
        leftnode.apply(this);
        boolean leftHasChanged = this.hasChanged.pop();

        this.hasChanged.push(false);
        rightnode.apply(this);
        boolean rightHasChanged = this.hasChanged.pop();

        if (leftHasChanged || rightHasChanged) {
            node.apply(this);
        }
    }
    }



    // converting constants to functions with empty arglist
    @Override
    public void caseAConstLterm(AConstLterm node) {
        ATermlist args = new ATermlist();
        AFunctAppLterm newNode = new AFunctAppLterm(node.getId(), null, null, args, null, null);
        node.replaceBy(newNode);
    }

    @Override
    public void caseAConstTterm(AConstTterm node) {
        ATermlist args = new ATermlist();
        AFunctAppTterm newNode = new AFunctAppTterm(node.getId(), null, null, args, null, null, null);
        node.replaceBy(newNode);
    }
}
