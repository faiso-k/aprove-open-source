package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class CaseAnalysisProof extends TheoremProverProof {

    protected Set<TheoremProverObligation> newObligations;

    public CaseAnalysisProof(){
    }

    public CaseAnalysisProof(Set<TheoremProverObligation> newObligations ) {
        this.newObligations = newObligations;

        this.name = "Case Analysis";
        this.shortName = this.name;
        this.longName  = this.name;

    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append(o.bold("Case analysis leads to the following new obligations:"));
        stringBuffer.append(o.paragraph());
        for(TheoremProverObligation theoremProverObligation : this.newObligations) {
            stringBuffer.append(o.export(theoremProverObligation));
            stringBuffer.append(o.export(o.paragraph()));
        }
        return stringBuffer.toString();
    }

    public Set<TheoremProverObligation> getNewObligations() {
        return this.newObligations;
    }

    public void setNewObligations(Set<TheoremProverObligation> newObligations) {
        this.newObligations = newObligations;
    }

    @Override
    public Proof deepcopy() {
        LinkedHashSet<TheoremProverObligation> obligations = new LinkedHashSet<TheoremProverObligation>();
        for(TheoremProverObligation theoremProverObligation : this.newObligations) {
            obligations.add(theoremProverObligation.deepcopy());
        }
        return new CaseAnalysisProof(obligations);
    }


}
