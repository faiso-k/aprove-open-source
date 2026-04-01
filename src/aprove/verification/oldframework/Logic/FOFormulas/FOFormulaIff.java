package aprove.verification.oldframework.Logic.FOFormulas;


/**
 * Logical equivalence of two FO formulas.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaIff extends FOFormula {
    protected FOFormula left;
    protected FOFormula right;

    public FOFormulaIff (FOFormula left, FOFormula right) {
        this.left  = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return "(IFF " + this.left.toString() + " " + this.right.toString() + ")";
    }

}
