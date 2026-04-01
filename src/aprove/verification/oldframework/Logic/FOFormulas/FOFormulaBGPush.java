package aprove.verification.oldframework.Logic.FOFormulas;


/**
 * Pushes a background formula to the set of axioms.
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaBGPush extends FOFormula {
    protected FOFormula background;

    public FOFormulaBGPush (FOFormula background) {
        this.background = background;
    }

    @Override
    public String toString() {
        return "(BGPUSH " + this.background.toString() + ")";
    }

}
