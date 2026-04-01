package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.theoremprover.TerminationProofs.*;


public class LemmaDatabaseProof extends TheoremProverProof {

    protected Formula formula;

    public LemmaDatabaseProof() {
    }

    public LemmaDatabaseProof(Formula formula) {
        super();

        this.shortName     = "Lemma Database";
        this.longName    = "Lemma Database";

        this.formula = formula;

    }

    @Override
    public String export(Export_Util o) {
        if (Proof.CACHE_VALUES) {
                if (this.result.length() != 0) {
                    return this.result.toString();
                }
        } else {
            this.startUp();
        }

        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append(o.bold("The formula is an instance of the following formula, which has already been proved or is supported by the lemma database:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.formula));

        return stringBuffer.toString();
    }

    public String toBibTeX() {
        return null;
    }

    public Formula getFormula() {
        return this.formula;
    }

    public void setFormula(Formula formula) {
        this.formula = formula;
    }

    @Override
    public Proof deepcopy() {
        return new LemmaDatabaseProof(this.formula.deepcopy());
    }

}
