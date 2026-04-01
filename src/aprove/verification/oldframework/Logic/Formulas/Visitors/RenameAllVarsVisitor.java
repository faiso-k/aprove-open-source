package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.*;

/**
 * renames all free variables in a formula. use the "apply" method of this
 * class. Note: This method and its subclass RenameAllVarsVisitor are
 * destructive
 *
 * @author Burak Emir, Eugen Yu
 * @version $Id$
 */

public class RenameAllVarsVisitor implements CoarseFormulaVisitor<Formula> {

    // knows the set of variables that are not to be used
    FreshVarGenerator fg;

    AlgebraSubstitution subs;

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return null;// do nothing
    }

    /*
     * modified by eugen
     */
    @Override
    public Formula caseEquation(Equation eqFormula) {

        Set<AlgebraVariable> svright = eqFormula.getLeft().getVars();
        Set<AlgebraVariable> svleft = eqFormula.getRight().getVars();
        svleft.addAll(svright);

        for (AlgebraVariable var : svleft) {
            AlgebraVariable newvar = this.fg.getFreshVariable(var, true);
            this.subs.put(var.getVariableSymbol(), newvar);
        }
        Formula asFormula = (Formula) eqFormula;
        Equation newEquation = (Equation) (asFormula.apply(this.subs));

        eqFormula.setLeft(newEquation.getLeft());
        eqFormula.setRight(newEquation.getRight());
        return null;
    }

    @Override
    public Formula caseJunctorFormula(JunctorFormula jFormula) {
        jFormula.getLeft().apply(this);
        if (!(jFormula instanceof Not)) {
            jFormula.getRight().apply(this);
        }
        return null;
    }

    public RenameAllVarsVisitor(Set<AlgebraVariable> sv) {
        this.fg = new FreshVarGenerator(sv);
        this.subs = AlgebraSubstitution.create();
    }

    public RenameAllVarsVisitor(FreshVarGenerator fg) {
        this.fg = fg;
        this.subs = AlgebraSubstitution.create();
    }

}
