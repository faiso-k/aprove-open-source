package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Proof for an indirect proof
 * (I can't help but the class name sounds stupid.)
 *
 * @author dickmeis
 * @version $Id$
 *
 */
public class IndirectProofProof extends TheoremProverProof {

    private TheoremProverObligation newObligation;

    public IndirectProofProof() {
    }

    public IndirectProofProof(TheoremProverObligation newObligation) {
        this.newObligation = newObligation;

        this.name      = "Indirect Proof";
        this.shortName = "Indirect Proof";
        this.longName  = "Indirect Proof";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("Instead the negation has to be disproven:"));
        stringBuffer.append(o.linebreak());

        stringBuffer.append(o.export(this.newObligation));

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        return new IndirectProofProof(this.newObligation.deepcopy());
    }

}
