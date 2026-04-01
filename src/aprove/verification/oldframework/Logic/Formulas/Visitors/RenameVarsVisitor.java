package aprove.verification.oldframework.Logic.Formulas.Visitors ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.*;

/** Renames all vars in a formula
 * @author dickmeis
 * @version $Id$
 */
public class RenameVarsVisitor implements CoarseFormulaVisitor<Object> {

    protected FreshVarGenerator fg;

    public RenameVarsVisitor(Set<AlgebraVariable> sv) {
        this.fg = new FreshVarGenerator(sv);
    }

    public RenameVarsVisitor(FreshVarGenerator fg) {
        this.fg = fg;
    }

    @Override
    public Object caseEquation(Equation eqFormula) {
        eqFormula.getLeft().renameVars(this.fg);
        eqFormula.getRight().renameVars(this.fg);
        return null;
    }

    @Override
    public Object caseJunctorFormula(JunctorFormula jFormula) {
        jFormula.getLeft().renameVars(this.fg);
        Formula right = jFormula.getRight();
        if(right != null){
            right.renameVars(this.fg);
        }
        return null;
    }

    @Override
    public Object caseTruthValue(FormulaTruthValue truthvalFormula) {
        return null;
    }

}
