package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class LemmaSpeculationProof extends TheoremProverProof {

    protected Formula lemma;
    protected Set<TheoremProverObligation> newObligations;

    public LemmaSpeculationProof(Formula lemma, Set<TheoremProverObligation> newObligations) {
        super();

        this.name           = "Lemma Speculation";
        this.longName     = "Lemma Speculation";
        this.shortName     = "Lemma Speculation";

        this.lemma  = lemma;
        this.newObligations = newObligations;

    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The following lemma was speculated:"))
        .append(o.linebreak())
        .append(o.export(this.lemma))
        .append(o.linebreak())
        .append(o.bold("This leads to the following new formula(s):"));
        for(TheoremProverObligation theoremProverObligation : this.newObligations) {
            stringBuffer.append(o.linebreak());
            stringBuffer.append(o.export(theoremProverObligation));
        }


        return stringBuffer.toString();

    }

    @Override
    public Proof deepcopy() {

        Set<TheoremProverObligation> theoremProverObligations = new LinkedHashSet<TheoremProverObligation>();
        for(TheoremProverObligation theoremProverObligation:this.newObligations){
            theoremProverObligations.add(theoremProverObligation.deepcopy());
        }

        return new LemmaSpeculationProof(this.lemma.deepcopy(), theoremProverObligations);
    }

}
