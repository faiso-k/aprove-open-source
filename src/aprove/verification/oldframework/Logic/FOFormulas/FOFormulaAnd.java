package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

/**
 * Conjunction of FO formulas.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaAnd extends FOFormula {
    protected List<FOFormula> formulas;

    public FOFormulaAnd (List<FOFormula> formulas) {
        this.formulas  = formulas;
    }

    @Override
    public String toString() {
        String s = "(AND";
        for (FOFormula f: this.formulas) {
            s += " "+f.toString();
        }
        return s+")";
    }
}
