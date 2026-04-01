package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class PushNegationInsideTransformer implements LinearFormulaVisitor<LinearFormula>{

    protected boolean notState;

    static LinearFormula apply(LinearFormula formula){
        PushNegationInsideTransformer transformer = new PushNegationInsideTransformer();

        LinearFormula newFormula = formula.apply(transformer);

        return newFormula;
    }

    public PushNegationInsideTransformer(boolean not){
        this.notState = not;
    }

    public PushNegationInsideTransformer(){
        this.notState = false;
    }

    @Override
    public LinearFormula caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {
        System.err.println("Forbidden to occur.");
        return null;
    }

    @Override
    public LinearFormula caseAnd(AndLinearFormula and) {

        LinearFormula left = and.getLeft();
        LinearFormula right = and.getRight();

        LinearFormula newLeft = left.apply(new PushNegationInsideTransformer(this.notState));
        LinearFormula newRight = right.apply(new PushNegationInsideTransformer(this.notState));

        if(this.notState){
            return new OrLinearFormula(newLeft, newRight);
        }
        else{
            return new AndLinearFormula(newLeft, newRight);
        }
    }

    @Override
    public LinearFormula caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {

        AlgebraVariable var = existentialLinearFormula.getVariable();
        LinearFormula sub = existentialLinearFormula.getSubFormula();
        LinearFormula newsub = sub.apply(new PushNegationInsideTransformer(false));

        ExistentialQuantifiedLinearFormula newFormula = new ExistentialQuantifiedLinearFormula(var, newsub);

        if(this.notState){
            return new NotLinearFormula(newFormula);
        }
        else{
            return newFormula;
        }
    }

    @Override
    public LinearFormula caseLinearConstraint(LinearConstraint linearConstraint) {
        if(this.notState){
            return linearConstraint.negate();
        }
        else{
            return linearConstraint.deepcopy();
        }
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {
        if(this.notState){
            return new NotLinearFormula(moduloLinearFormula);
        }
        else{
            return moduloLinearFormula.deepcopy();
        }
    }

    @Override
    public LinearFormula caseNot(NotLinearFormula not) {

        LinearFormula sub = not.getSubFormula();

        LinearFormula newsub = sub.apply(new PushNegationInsideTransformer(!this.notState));

        return newsub;
    }

    @Override
    public LinearFormula caseOr(OrLinearFormula or) {
        LinearFormula left = or.getLeft();
        LinearFormula right = or.getRight();

        LinearFormula newLeft = left.apply(new PushNegationInsideTransformer(this.notState));
        LinearFormula newRight = right.apply(new PushNegationInsideTransformer(this.notState));

        if(this.notState){
            return new AndLinearFormula(newLeft, newRight);
        }
        else{
            return new OrLinearFormula(newLeft, newRight);
        }
    }

    @Override
    public LinearFormula caseTruthValue(TruthValueLinearFormula truthvalue) {

        if(this.notState){
            boolean b = truthvalue.getValue();
            return new TruthValueLinearFormula(!b);
        }
        else{
            return truthvalue.deepcopy();
        }
    }

}
