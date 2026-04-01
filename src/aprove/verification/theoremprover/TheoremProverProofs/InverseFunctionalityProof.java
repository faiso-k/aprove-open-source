package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class InverseFunctionalityProof extends TheoremProverProof {

    protected Set<TheoremProverObligation> newObligations;

    public InverseFunctionalityProof(Set<TheoremProverObligation> newObligations) {
        super();

        this.shortName = "Inverse Functionality";
        this.longName  = "Inverse Functionality";

        this.newObligations = newObligations;

    }

    @Override
    public String export(Export_Util o) {
        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("Formula could be geeralised by inverse functionality to the following new obligation:"));
        for(TheoremProverObligation newObligation : this.newObligations) {
            stringBuffer.append(o.export(newObligation));
            stringBuffer.append(o.linebreak());
        }
        stringBuffer.append(o.export(o.paragraph()));
        return stringBuffer.toString();

    }

    public String toBibTeX() {
        return null;
    }

    public Set<TheoremProverObligation> getNewObligation() {
        return this.newObligations;
    }

    public void setNewObligations(Set<TheoremProverObligation> newObligations) {
        this.newObligations = newObligations;
    }

    @Override
    public Proof deepcopy() {

        Set<TheoremProverObligation> copy = new LinkedHashSet<TheoremProverObligation>();
        for(TheoremProverObligation theoremProverObligation : this.newObligations) {
            copy.add(theoremProverObligation.deepcopy());
        }

        return new InverseFunctionalityProof(copy);
    }

}
