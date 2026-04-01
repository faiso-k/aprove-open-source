package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class AllQuantifiedLinearFormula extends QuantifiedLinearFormula{

    @Override
    public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseAllQuantifiedLinearFormula( this );
    }

    public AllQuantifiedLinearFormula(AlgebraVariable variable, LinearFormula formula){
        this.variable = (AlgebraVariable) variable.deepcopy();
        this.subFormula = formula;
    }

    public static LinearFormula create(Collection<AlgebraVariable> allqunatifiedlVariables, LinearFormula formula) {
        if(allqunatifiedlVariables.isEmpty()){
            return formula;
        }
        else{
            LinearFormula res = formula;

            for (AlgebraVariable variable : allqunatifiedlVariables) {
                res = new AllQuantifiedLinearFormula(variable, res);
            }

            return res;
        }
    }

    @Override
    public LinearFormula deepcopy() {
        return new AllQuantifiedLinearFormula(
                (AlgebraVariable)this.variable.deepcopy(), this.subFormula.deepcopy());
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("A ");
        sb.append(this.variable.getName());
        sb.append(" ");
        sb.append(this.subFormula);

        return sb.toString();
    }
}
