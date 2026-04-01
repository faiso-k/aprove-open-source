package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Conjunction of a FO formula for a given set of variables.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaForall extends FOFormulaQuantifier {

    public FOFormulaForall (List<TRSVariable> vars, FOFormula formula) {
        super(vars, formula);
    }

    @Override
    public String toString() {
        return "(FORALL " + super.toString() + ")";
    }

}
