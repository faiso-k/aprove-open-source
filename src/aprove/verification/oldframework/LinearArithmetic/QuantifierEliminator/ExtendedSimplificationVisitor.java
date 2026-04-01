package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class ExtendedSimplificationVisitor implements LinearFormulaVisitor<Object>{

    LinearIntegerConstraintSimplifier lics = new LinearIntegerConstraintSimplifier();
    boolean ok = true;

    public static List<Dissolving> apply(LinearFormula formula){
        ExtendedSimplificationVisitor esv = new ExtendedSimplificationVisitor();
        formula.apply(esv);
        if(!esv.ok){
            return null;
        }

        boolean solveable = esv.lics.simplify();

        if (!solveable){
            return null;
        }
        else{
            ArrayList<LinearConstraint> allConstraints = esv.lics.getAllConstraints();
            if (!allConstraints.isEmpty()){
                return null;
            }
            else{
                return esv.lics.getDissolvings();
            }
        }
    }

    @Override
    public Object caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {
        this.ok = false;
        return null;
    }

    @Override
    public LinearFormula caseAnd(AndLinearFormula and) {
        and.getLeft().apply(this);
        and.getRight().apply(this);

        return null;
    }

    @Override
    public LinearFormula caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {
        this.ok = false;
        return null;
    }

    @Override
    public LinearFormula caseLinearConstraint(LinearConstraint linearConstraint) {
        this.lics.addConstraint(linearConstraint);
        return null;
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {
        this.ok = false;
        return null;
    }

    @Override
    public LinearFormula caseNot(NotLinearFormula not) {
        this.ok = false;
        return null;
    }

    @Override
    public LinearFormula caseOr(OrLinearFormula or) {
        this.ok = false;
        return null;
    }

    @Override
    public LinearFormula caseTruthValue(TruthValueLinearFormula truthvalue) {
        this.ok = false;
        return null;
    }

}
