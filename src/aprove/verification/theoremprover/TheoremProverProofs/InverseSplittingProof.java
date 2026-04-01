package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class InverseSplittingProof extends TheoremProverProof {

    protected TheoremProverObligation newObligation;

    public InverseSplittingProof(TheoremProverObligation newObligation) {
        super();

        this.longName  = "Inverse Splitting";
        this.shortName = "Inverse Splitting";

        this.newObligation = newObligation;
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The formula coudld be generalised by using inverse splitting to the following new obligations:"));
        stringBuffer.append(o.export(this.newObligation));
        stringBuffer.append(o.paragraph());

        return stringBuffer.toString();

    }

    public String toBibTeX() {
        return null;
    }

    @Override
    public Proof deepcopy() {
        return new InverseSplittingProof(this.newObligation.deepcopy());
    }
}
