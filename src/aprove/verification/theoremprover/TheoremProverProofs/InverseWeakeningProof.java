package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class InverseWeakeningProof extends TheoremProverProof {

    protected TheoremProverObligation newObligation;

    public InverseWeakeningProof(TheoremProverObligation newObligation) {
        super();

        this.shortName = "Inverse Weakening";
        this.longName  = "Inverse Weakening";

        this.newObligation = newObligation;

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

        stringBuffer.append(o.bold("The formula could be generalised by inverse weakening to the following new obligations:"));
        stringBuffer.append(o.export(this.newObligation));
        stringBuffer.append(o.paragraph());


        return stringBuffer.toString();

    }

    public String toBibTeX() {
        return null;
    }

    public TheoremProverObligation getNewObligations() {
        return this.newObligation;
    }

    public void setNewObligations(TheoremProverObligation newObligation) {
        this.newObligation = newObligation;
    }

    @Override
    public Proof deepcopy() {
        return new InverseWeakeningProof(this.newObligation.deepcopy());
    }

}
