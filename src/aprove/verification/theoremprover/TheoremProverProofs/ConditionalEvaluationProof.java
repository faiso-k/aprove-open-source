package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class ConditionalEvaluationProof extends TheoremProverProof {

    private Set<TheoremProverObligation> newObligations;

    public ConditionalEvaluationProof() {
    }

    public ConditionalEvaluationProof(Set<TheoremProverObligation> newObligations) {
        this.newObligations = newObligations;

        this.name      = "Conditional Evaluation";
        this.shortName = "Conditional Evaluation";
        this.longName  = "Conditional Evaluation";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The formula could be reduced to the following new obligations by conditional evaluation:"));
        stringBuffer.append(o.linebreak());
        for(TheoremProverObligation theoremProverObligation : this.newObligations) {
            stringBuffer.append(o.export(theoremProverObligation));
            stringBuffer.append(o.paragraph());
        }
        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        Set<TheoremProverObligation> obligations = new LinkedHashSet<TheoremProverObligation>();
        for(TheoremProverObligation theoremProverObligation : this.newObligations) {
            obligations.add(theoremProverObligation.deepcopy());
        }

        return new ConditionalEvaluationProof(obligations);
    }

    public Set<TheoremProverObligation> getNewObligations() {
        return this.newObligations;
    }

    public void setNewObligations(Set<TheoremProverObligation> newObligations) {
        this.newObligations = newObligations;
    }

}
