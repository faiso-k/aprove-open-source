package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class DissolvingsApplicator implements LinearFormulaVisitor<LinearFormula>{

    List<Dissolving> dissolvings;

    public DissolvingsApplicator(List<Dissolving> dissolvings){
        this.dissolvings = dissolvings;
    }

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

        LinearConstraint newConstraint = linearConstraint.deepcopy();

        for (Dissolving dissolving : this.dissolvings) {
            newConstraint = newConstraint.applyDissolving(dissolving);
        }

        return newConstraint;
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {

        ModuloLinearFormula newModuloLinearFormula = moduloLinearFormula.deepcopy();

        for (Dissolving dissolving : this.dissolvings) {
            newModuloLinearFormula = newModuloLinearFormula.applyDissolving(dissolving);
        }

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
