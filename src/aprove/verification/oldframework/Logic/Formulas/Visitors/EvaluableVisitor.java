package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * Decides whether a formula is evaluable for a given evaluator.
 *
 * This visitor does now work of GetAllNegationsVisitor,
 * GetAllAndOrFormulasVisitor and GetAllEquationsVisitor in parallel.
 *
 * GetAllNegationsVisitor GetAllAndOrFormulasVisitor are now no longer needed.
 *
 * @author dickmeis
 * @version $Id$
 */

public class EvaluableVisitor implements CoarseFormulaVisitor<Formula> {

    protected Boolean evaluable = false;
    protected Evaluator ev;

    public static Boolean applyTo(final Formula f, final Evaluator ev) {
        final EvaluableVisitor vis = new EvaluableVisitor();
        vis.ev = ev;
        f.apply(vis);
        return vis.evaluable;
    }

    @Override
    public Formula caseTruthValue(final FormulaTruthValue truthvalFormula) {
        return null;
    }

    @Override
    public Formula caseEquation(final Equation eqFormula) {
        if (eqFormula.evaluable(this.ev)) {
            this.evaluable = true;
        }
        return null;
    }

    @Override
    public Formula caseJunctorFormula(final JunctorFormula jFormula) {
        if (jFormula instanceof Not) {
            if (jFormula.getLeft() instanceof FormulaTruthValue) {
                this.evaluable = true;
                return null;
            }
        }

        if (jFormula instanceof And || jFormula instanceof Or) {
            if (jFormula.getLeft() instanceof FormulaTruthValue) {
                this.evaluable = true;
                return null;
            }
            if (jFormula.getRight() instanceof FormulaTruthValue) {
                this.evaluable = true;
                return null;
            }
        }

        if (jFormula.getLeft() != null) {
            jFormula.getLeft().apply(this);
        }
        if (jFormula.getRight() != null && !this.evaluable) {
            jFormula.getRight().apply(this);
        }

        return null;
    }
}
