package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class ExistentialQuantifiedLinearFormula extends QuantifiedLinearFormula{

    @Override
    public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseExistentialQuantifiedLinearFormula( this );
    }

    public ExistentialQuantifiedLinearFormula(AlgebraVariable variable, LinearFormula formula){
        this.variable = (AlgebraVariable) variable.deepcopy();
        this.subFormula = formula;
    }

    @Override
    public LinearFormula deepcopy() {
        return new ExistentialQuantifiedLinearFormula(
                (AlgebraVariable)this.variable.deepcopy(), this.subFormula.deepcopy());
    }

    public static LinearFormula create(Collection<AlgebraVariable> existentialVariables, LinearFormula formula) {
        if(existentialVariables.isEmpty()){
            return formula;
        }
        else{
            LinearFormula res = formula;

            for (AlgebraVariable variable : existentialVariables) {
                res = new ExistentialQuantifiedLinearFormula(variable, res);
            }

            return res;
        }
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("E ");
        sb.append(this.variable.getName());
        sb.append(" ");
        sb.append(this.subFormula);

        return sb.toString();
    }
}
