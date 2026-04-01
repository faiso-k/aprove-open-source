package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class ToMinusInfinityTransformer implements LinearFormulaVisitor<LinearFormula>{

    protected AlgebraVariable variable;

    protected int substitutionValue;

    public ToMinusInfinityTransformer(AlgebraVariable var, int value){
        this.variable = var;
        this.substitutionValue = value;
    }

    @Override
    public LinearFormula caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {

        System.err.println("May not occur");
        return null;
    }

    @Override
    public LinearFormula caseAnd(AndLinearFormula and) {

        LinearFormula left = and.getLeft().apply(this);
        LinearFormula right = and.getRight().apply(this);

        return new AndLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {

        System.err.println("May not occur");
        return null;
    }

    @Override
    public LinearFormula caseLinearConstraint(LinearConstraint linearConstraint) {
        Map<AlgebraVariable, Rational> coeffs = linearConstraint.getCoefficients();

        Rational value = coeffs.remove(this.variable);

        if(value == null){
            return (LinearConstraint) linearConstraint.deepcopy();
        }
        else{
            int intvalue = value.getNumerator();
            if(intvalue > 0){
                // type A
                return TruthValueLinearFormula.TRUE;
            }
            else{
                // type B
                return TruthValueLinearFormula.FALSE;
            }
        }
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {

        ModuloLinearFormula newModuloLinearFormula = moduloLinearFormula.applySubstitution(this.variable, this.substitutionValue);

        return newModuloLinearFormula;
    }

    @Override
    public LinearFormula caseNot(NotLinearFormula not) {
        LinearFormula subformula = not.getSubFormula().apply(this);
        return new NotLinearFormula(subformula);
    }

    @Override
    public LinearFormula caseOr(OrLinearFormula or) {
        LinearFormula left = or.getLeft().apply(this);
        LinearFormula right = or.getRight().apply(this);

        return new OrLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseTruthValue(TruthValueLinearFormula truthvalue) {
        return truthvalue.deepcopy();
    }

}
