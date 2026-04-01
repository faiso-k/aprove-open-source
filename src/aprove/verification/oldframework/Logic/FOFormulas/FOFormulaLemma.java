package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

/**
 * A Lemma is a set of formulas, where each formula is proven given the previous formulas.
 * If all formulas can be proven the last one will be used.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaLemma extends FOFormula {
    protected List<FOFormula> formulas;

    public FOFormulaLemma (List<FOFormula> formulas) {
        this.formulas  = formulas;
    }

    @Override
    public String toString() {
        String s = "(LEMMA";
        for (FOFormula f : this.formulas) {
            s += " " + this.formulas.toString();
        }
        return s + ")";
    }

}
