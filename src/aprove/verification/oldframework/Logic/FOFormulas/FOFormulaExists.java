package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Disjunction of a FO formula for a given set of variables.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaExists extends FOFormulaQuantifier {
    public FOFormulaExists (List<TRSVariable> vars, FOFormula formula) {
        super(vars, formula);
    }

    @Override
    public String toString() {
        return "(EXISTS " + super.toString() + ")";
    }

}
