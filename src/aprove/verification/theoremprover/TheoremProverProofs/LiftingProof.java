package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class LiftingProof extends TheoremProverProof {

    protected TheoremProverObligation newObligation;

    public LiftingProof() {
    }

    public LiftingProof(TheoremProverObligation newObligation) {
        this.name         = "Hypothesis Lifting";
        this.shortName     = this.name;
        this.longName      = this.name;

        this.newObligation = newObligation;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append(o.bold("Formula could be generalised by hypothesis lifting to the following new obligation:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation));
        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        return new LiftingProof(this.newObligation.deepcopy());
    }

    public TheoremProverObligation getNewObligation() {
        return this.newObligation;
    }

    public void setNewObligation(TheoremProverObligation newObligation) {
        this.newObligation = newObligation;
    }


}
