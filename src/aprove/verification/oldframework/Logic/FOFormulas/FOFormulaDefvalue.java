package aprove.verification.oldframework.Logic.FOFormulas;

/**
 * Defvalue
 * @author Andreas Kelle-Emden
 */
public class FOFormulaDefvalue extends FOFormula {
    protected String id;
    public FOFormulaDefvalue(String id) {
        this.id = id;
    }

    @Override
    public String toString() {
        return "(DEFVALUE " + this.id + ")";
    }
}
