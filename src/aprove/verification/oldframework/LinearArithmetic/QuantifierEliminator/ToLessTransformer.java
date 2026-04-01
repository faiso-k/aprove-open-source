package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class ToLessTransformer implements LinearFormulaVisitor<LinearFormula>{

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

        LinearConstraint constraint = LinearIntegerConstraintSimplifier.toIntegerNormalForm(linearConstraint);

        ConstraintType ct = constraint.getConstraintType();
        if(ct.equals(ConstraintType.LESSEQ)){
            Rational newconstant = constraint.getConstant().plus(new Rational(1));

            LinearConstraint newConstraint =
                new LinearConstraint(constraint.getCoefficients(), ConstraintType.LESS, newconstant);

            return newConstraint;
        }
        else if(ct.equals(ConstraintType.EQUALITY)){
            LinearConstraint constraint1 = constraint.changeConstraintType(ConstraintType.LESSEQ);
            LinearConstraint constraint2 = constraint.changeConstraintType(ConstraintType.GREATEREQ);

            AndLinearFormula and = new AndLinearFormula(constraint1, constraint2);

            LinearFormula res = and.apply(this);

            return res;
        }
        else if(ct.equals(ConstraintType.INEQUALITY)){
            LinearConstraint constraint1 = constraint.changeConstraintType(ConstraintType.LESS);
            LinearConstraint constraint2 = constraint.changeConstraintType(ConstraintType.GREATER);

            OrLinearFormula or = new OrLinearFormula(constraint1, constraint2);

            LinearFormula res = or.apply(this);

            return res;
        }
        else{
            System.err.println("");
            return null;
        }
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {
        return moduloLinearFormula.deepcopy();
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
