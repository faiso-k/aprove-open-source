package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class InverseModusPonensProof extends TheoremProverProof {

    protected TheoremProverObligation newObligation;

    protected Formula lemma;

    public InverseModusPonensProof(TheoremProverObligation newObligation, Formula lemma) {
        super();

        this.lemma = lemma;
        this.newObligation = newObligation;

    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("Could be generalised to the following formula by using inverse modus ponens:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.bold("The following lemma was used:"));
        stringBuffer.append(o.export(this.lemma));

        return stringBuffer.toString();

    }

    @Override
    public Proof deepcopy() {
        return new InverseModusPonensProof(this.newObligation.deepcopy(), this.lemma.deepcopy());
    }

}
