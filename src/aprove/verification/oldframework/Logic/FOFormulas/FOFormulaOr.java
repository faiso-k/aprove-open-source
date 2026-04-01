package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

/**
 * Disjunction of FO formulas.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaOr extends FOFormula {
    protected List<FOFormula> formulas;

    public FOFormulaOr (List<FOFormula> formulas) {
        this.formulas  = formulas;
    }

    @Override
    public String toString() {
        String s = "(OR";
        for (FOFormula f: this.formulas) {
            s += " "+f.toString();
        }
        return s+")";
    }

}
