package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class OrLinearFormula extends LinearFormula{
    protected LinearFormula left;
    protected LinearFormula right;

    public OrLinearFormula(LinearFormula left, LinearFormula right) {
        this.left = left;
        this.right = right;
    }

    public static LinearFormula create(List<LinearFormula> disjunctions) {
        if(disjunctions.size()==0) {
            return null;
        }else if(disjunctions.size()==1){
            return disjunctions.get(0);
        }else{
            OrLinearFormula or = new OrLinearFormula(disjunctions.get(0), disjunctions.get(1));
            for(int i=2; i < disjunctions.size(); i++) {
                or = new OrLinearFormula(or, disjunctions.get(i));
            }
            return or;
        }
    }

    @Override
    final public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseOr( this );
    }

    @Override
    public LinearFormula deepcopy() {
        return new OrLinearFormula(this.left.deepcopy(), this.right.deepcopy());
    }

    /**
     * @return the left
     */
    public LinearFormula getLeft() {
        return this.left;
    }

    /**
     * @return the right
     */
    public LinearFormula getRight() {
        return this.right;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("( ");
        sb.append(this.left);
        sb.append(" \\/ ");
        sb.append(this.right);
        sb.append(" )");

        return sb.toString();
    }
}
