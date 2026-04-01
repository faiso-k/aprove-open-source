package aprove.verification.oldframework.Logic.FOFormulas;

/**
 * Qualified FO formula.
 * @author Andreas Kelle-Emden
 */
public class FOFormulaITE extends FOFormula {
    protected FOFormula cond_formula;
    protected FOFormula then_formula;
    protected FOFormula else_formula;

    public FOFormulaITE (FOFormula cond_formula, FOFormula then_formula, FOFormula else_formula) {
        this.cond_formula = cond_formula;
        this.then_formula = then_formula;
        this.else_formula = else_formula;
    }

    @Override
    public String toString() {
        return "(IF " + this.cond_formula + " THEN " + this.then_formula + " ELSE " + this.else_formula + ")";
    }
}
