package aprove.verification.oldframework.Logic.FOFormulas;


/**
 * Negation of a FO formula.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaNot extends FOFormula {
    protected FOFormula formula;

    public FOFormulaNot (FOFormula formula) {
        this.formula = formula;
    }

    @Override
    public String toString() {
        return "(NOT " + this.formula.toString() + ")";
    }

}
