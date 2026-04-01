package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Logic.Formulas.*;

public class FormulaSizeVisitor implements CoarseFormulaVisitor<Integer> {

    public static int apply(Formula formula) {
        return formula.apply(new FormulaSizeVisitor());
    }

    @Override
    public Integer caseEquation(Equation eqFormula) {
        return 1+eqFormula.getLeft().size()+eqFormula.getRight().size();
    }

    @Override
    public Integer caseJunctorFormula(JunctorFormula jFormula) {
        return jFormula.getRight() == null ? 1+jFormula.getLeft().getSize() :
            1+jFormula.getRight().getSize()+jFormula.getLeft().getSize();
    }

    @Override
    public Integer caseTruthValue(FormulaTruthValue truthvalFormula) {
        return 1;
    }

}
