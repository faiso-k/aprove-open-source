package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

/**
 * A proof is a list of formulas, where formula n is implied by formulas 1, ..., n-1.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaProof extends FOFormula {
    protected List<FOFormula> formulas;

    public FOFormulaProof (List<FOFormula> formulas) {
        this.formulas = formulas;
    }

    @Override
    public String toString() {
        String s = "(PROOF";
        for (FOFormula f: this.formulas) {
            s += " "+f.toString();
        }
        return s+")";
    }

}
