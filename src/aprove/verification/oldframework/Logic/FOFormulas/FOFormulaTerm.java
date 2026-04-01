package aprove.verification.oldframework.Logic.FOFormulas;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Term can be a pure term or a literal
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaTerm extends FOFormula {
    protected TRSTerm term;

    public FOFormulaTerm (TRSTerm term) {
        this.term = term;
    }

    public TRSTerm getTerm() {
        return this.term;
    }

    @Override
    public String toString(){
        return this.term.toString();
    }
}