package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class SimplificationVisitor implements LinearFormulaVisitor<LinearFormula>{

    @Override
    public LinearFormula caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {
        LinearFormula subformula = allLinearFormula.getSubFormula();
        LinearFormula newsubformula = subformula.apply(this);

        return new AllQuantifiedLinearFormula(allLinearFormula.getVariable(), newsubformula);
    }

    @Override
    public LinearFormula caseAnd(AndLinearFormula and) {

        LinearFormula left = and.getLeft().apply(this);
        LinearFormula right = and.getRight().apply(this);

        if(left.equals(TruthValueLinearFormula.TRUE)){
            return right;
        }
        if(left.equals(TruthValueLinearFormula.FALSE)){
            return TruthValueLinearFormula.FALSE;
        }
        if(right.equals(TruthValueLinearFormula.TRUE)){
            return left;
        }
        if(right.equals(TruthValueLinearFormula.FALSE)){
            return TruthValueLinearFormula.FALSE;
        }

        if(right.equals(left)){
            return left;
        }

        return new AndLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {
        LinearFormula subformula = existentialLinearFormula.getSubFormula();
        LinearFormula newsubformula = subformula.apply(this);

        return new ExistentialQuantifiedLinearFormula(existentialLinearFormula.getVariable(), newsubformula);
    }

    @Override
    public LinearFormula caseLinearConstraint(LinearConstraint linearConstraint) {

        Map<AlgebraVariable, Rational> coeffs = linearConstraint.getCoefficients();

        if(coeffs.isEmpty()){
            int c = linearConstraint.getConstant().getNumerator();

            if(0 < c){
                return TruthValueLinearFormula.TRUE;
            }
            else{
                return TruthValueLinearFormula.FALSE;
            }
        }

        int constant = linearConstraint.getConstant().getNumerator();

        if(constant == 0){
            boolean pos = true;

            for (Entry<AlgebraVariable, Rational> entry : coeffs.entrySet()) {
                int n = entry.getValue().getNumerator();

                if(n<0){
                    pos = false;
                    break;
                }
            }

            if(pos){
                 // a+b+c < 0
                return TruthValueLinearFormula.FALSE;
            }
        }

        return linearConstraint.deepcopy();

    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {
        Map<AlgebraVariable, Integer> coeffs = moduloLinearFormula.getCoefficients();

        if(coeffs.isEmpty()){
            int modulo = moduloLinearFormula.getModulo();
            int constant = moduloLinearFormula.getConstant();

            int m = constant % modulo;

            if(m==0){
                return TruthValueLinearFormula.TRUE;
            }
            else{
                return TruthValueLinearFormula.FALSE;
            }
        }
        else{
            return moduloLinearFormula.deepcopy();
        }
    }

    @Override
    public LinearFormula caseNot(NotLinearFormula not) {
        LinearFormula subformula = not.getSubFormula().apply(this);

        if(subformula.equals(TruthValueLinearFormula.TRUE)){
            return TruthValueLinearFormula.FALSE;
        }
        if(subformula.equals(TruthValueLinearFormula.FALSE)){
            return TruthValueLinearFormula.TRUE;
        }

        return new NotLinearFormula(subformula);
    }

    @Override
    public LinearFormula caseOr(OrLinearFormula or) {
        LinearFormula left = or.getLeft().apply(this);
        LinearFormula right = or.getRight().apply(this);

        if(left.equals(TruthValueLinearFormula.TRUE)){
            return TruthValueLinearFormula.TRUE;
        }
        if(left.equals(TruthValueLinearFormula.FALSE)){
            return right;
        }
        if(right.equals(TruthValueLinearFormula.TRUE)){
            return TruthValueLinearFormula.TRUE;
        }
        if(right.equals(TruthValueLinearFormula.FALSE)){
            return left;
        }

        if(right.equals(left)){
            return left;
        }

        return new OrLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseTruthValue(TruthValueLinearFormula truthvalue) {
        return truthvalue.deepcopy();
    }

}
