package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

/**
 * Set of FO formulas
 * @author Andreas Kelle-Emden
 */
public class FOFormulaSet {
    private List<FOFormula> formulas;

    public FOFormulaSet() {
        this.formulas = new ArrayList<FOFormula>();
    }

    /**
     * Adds a FO formula to the set
     * @param formula FO formula to be added
     */
    public void add(FOFormula formula) {
        this.formulas.add(formula);
    }

    public List<FOFormula> getFormulas() {
        return this.formulas;
    }

    @Override
    public String toString(){
        String s = "";
        for (FOFormula f : this.formulas) {
            s += f.toString() + "\n";
        }
        return s;
    }
}