package aprove.verification.oldframework.Logic.FOFormulas;


/**
 * Logical implication.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaImplies extends FOFormula {
    protected FOFormula left;
    protected FOFormula right;

    public FOFormulaImplies (FOFormula left, FOFormula right) {
        this.left  = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return "(IMPLIES " + this.left.toString() + " " + this.right.toString() + ")";
    }

}
