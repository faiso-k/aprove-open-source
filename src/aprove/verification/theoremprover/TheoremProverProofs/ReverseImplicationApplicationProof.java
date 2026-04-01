package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Proof for LA lemma insertion
 *
 * @author dickmeis
 * @version $Id$
 *
 */

public class ReverseImplicationApplicationProof extends TheoremProverProof {

    TheoremProverObligation obligation;
    Formula implication;

    public ReverseImplicationApplicationProof(Formula implication, TheoremProverObligation obligation) {
        this.implication = implication;
        this.obligation = obligation;

        this.name      = "Reverse Implication Application";
        this.shortName = "Reverse Implication Application";
        this.longName  = "Reverse Implication Application";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("Applying the implication "));
        stringBuffer.append(o.newline());
        stringBuffer.append(o.export(this.implication));
        stringBuffer.append(o.newline());
        stringBuffer.append(o.bold("from left to right yields in the new obligation"));
        stringBuffer.append(o.newline());
        stringBuffer.append(o.newline());
        stringBuffer.append(o.export(this.obligation));

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        return new ReverseImplicationApplicationProof(this.implication.deepcopy(),
                                                      this.obligation.deepcopy());
    }
}
