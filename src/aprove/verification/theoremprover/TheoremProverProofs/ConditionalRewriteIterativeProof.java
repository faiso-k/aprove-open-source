/**
 * scetch for ConditionalRewritingProcessor when the ItearativeProcessor can be used
 *
 * meanwhile a workaround is used
 */

package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Proof for one conditional rewriting try
 *
 * @author dickmeis
 * @version $Id$
 */

public class ConditionalRewriteIterativeProof extends TheoremProverProof {

    private Pair<TheoremProverObligation, TheoremProverObligation> newObligation;

    public ConditionalRewriteIterativeProof() {
    }

    public ConditionalRewriteIterativeProof(Pair<TheoremProverObligation, TheoremProverObligation> newObligation) {
        this.newObligation = newObligation;

        this.name      = "Conditional Rewriting";
        this.shortName = "Conditional Rewriting";
        this.longName  = "Conditional Rewriting";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("If the following obligations can be proved"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation.x));
        stringBuffer.append(o.bold("it is equivalent to prove the obligation:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation.y));

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {

        Pair<TheoremProverObligation, TheoremProverObligation> newNewObligation =
            new Pair<TheoremProverObligation, TheoremProverObligation>(
                    this.newObligation.x.deepcopy(),
                    this.newObligation.y.deepcopy());

        return new ConditionalRewriteIterativeProof(newNewObligation);
    }
}
