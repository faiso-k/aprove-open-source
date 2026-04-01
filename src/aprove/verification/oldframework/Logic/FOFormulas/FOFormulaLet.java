
package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

/**
 * FO formula with a let-expression
 * @author Andreas Kelle-Emden
 */
public class FOFormulaLet extends FOFormula {
    protected List<String> ids;
    protected List<FOFormula> formulas;
    protected FOFormula formula;

    public FOFormulaLet (List<String> ids, List<FOFormula> formulas, FOFormula formula) {
        this.ids      = ids;
        this.formulas = formulas;
        this.formula  = formula;
    }

    @Override
    public String toString() {
        String s = "(LET";
        int size = this.formulas.size();
        for (int i = 0; i < size; i++) {
            s += " (" + this.ids.get(i) + " " + this.formulas.get(i).toString() + ")";
        }
        return s + " IN " + this.formula.toString() + ")";
    }

}
