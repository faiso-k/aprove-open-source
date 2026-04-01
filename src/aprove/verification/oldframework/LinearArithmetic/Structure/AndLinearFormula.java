package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class AndLinearFormula extends LinearFormula{

    protected LinearFormula left;

    protected LinearFormula right;

    @Override
    final public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseAnd( this );
    }

    public AndLinearFormula(LinearFormula left, LinearFormula right) {
        this.left = left;
        this.right = right;
    }

    public static LinearFormula create(List<LinearFormula> conjunctions) {
        if(conjunctions.size()==0) {
            return null;
        }else if(conjunctions.size()==1){
            return conjunctions.get(0);
        }else{
            AndLinearFormula and = new AndLinearFormula(conjunctions.get(0), conjunctions.get(1));
            for(int i=2; i < conjunctions.size(); i++) {
                and = new AndLinearFormula(and, conjunctions.get(i));
            }
            return and;
        }
    }

    @Override
    public LinearFormula deepcopy() {
        return new AndLinearFormula(this.left.deepcopy(), this.right.deepcopy());
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
        sb.append(" /\\ ");
        sb.append(this.right);
        sb.append(" )");

        return sb.toString();
    }

}
