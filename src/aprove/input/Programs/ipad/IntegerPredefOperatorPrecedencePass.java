package aprove.input.Programs.ipad;

import java.util.*;

import aprove.input.Generated.ipad.node.*;
import aprove.input.Programs.Predef.*;

/** Pass that rearranges the tree according to the operator precedences defined in PredefFunctionSymbols
 * a higher precendence indicates a stronger binding
 */
public class IntegerPredefOperatorPrecedencePass extends Pass {

    private Stack<Boolean> hasChanged = new Stack<Boolean>();


    @Override
    public void inStart(Start node) {
        this.hasChanged.push(false);
    }


    @Override
    public void caseAOperatorAppTerm(AOperatorAppTerm node) {

        boolean hasChangedNow;

        do {
            hasChangedNow = false;
            if (node.getRight() instanceof AOperatorAppTerm) {
                String topOp = this.chop(node.getInfixid());
                AOperatorAppTerm opRightNode = (AOperatorAppTerm)node.getRight();
                String rightOp = this.chop(opRightNode.getInfixid());
                Integer topOpPrecedence = PredefFunctionSymbols.getPrecedence(topOp);
                Integer rightOpPrecedence = PredefFunctionSymbols.getPrecedence(rightOp);

                // since the tree is built in a right-associative way, using ">=" will transform it into left-associative form
                if ( (topOpPrecedence != null) && (rightOpPrecedence != null) && (topOpPrecedence.intValue() >= rightOpPrecedence.intValue()) ) {
                    AStermTerm movedLeftToRight = new AStermTerm(opRightNode.getLeft());
                    AOperatorAppTerm newOpAppTerm = new AOperatorAppTerm(node.getLeft(), node.getInfixid(), movedLeftToRight);
                    ABracesSterm newLeftNode = new ABracesSterm(new TOpen(), newOpAppTerm, new TClose());

                    node.setInfixid(opRightNode.getInfixid());
                    node.setLeft(newLeftNode);
                    node.setRight(opRightNode.getRight());

                    hasChangedNow = true;

                    if (!this.hasChanged.peek()) {
                        this.hasChanged.pop();
                        this.hasChanged.push(true);
                    }
                }
            }
        } while (hasChangedNow);

        this.hasChanged.push(false);
        node.getLeft().apply(this);
        if (this.hasChanged.pop()) {
            node.apply(this);
        }

        this.hasChanged.push(false);
        node.getRight().apply(this);
        if (this.hasChanged.pop()) {
            node.apply(this);
        }
    }

}
