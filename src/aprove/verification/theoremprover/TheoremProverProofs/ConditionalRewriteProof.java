package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

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
 *
 */

public class ConditionalRewriteProof extends TheoremProverProof {

    private List<Pair<TheoremProverObligation, TheoremProverObligation>> newObligations;

    public ConditionalRewriteProof() {
    }

    public ConditionalRewriteProof(List<Pair<TheoremProverObligation, TheoremProverObligation>> newObligations) {
        this.newObligations = newObligations;

        this.name      = "Conditional Rewriting";
        this.shortName = "Conditional Rewriting";
        this.longName  = "Conditional Rewriting";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        for(Pair<TheoremProverObligation, TheoremProverObligation> pair : this.newObligations) {
            stringBuffer.append(o.bold("If the following obligations can be proved"));
            stringBuffer.append(o.linebreak());
            stringBuffer.append(o.export(pair.x));
            stringBuffer.append(o.bold("it is equivalent to prove the obligation:"));
            stringBuffer.append(o.linebreak());
            stringBuffer.append(o.export(pair.y));

            stringBuffer.append(o.paragraph());
        }
        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        List<Pair<TheoremProverObligation, TheoremProverObligation>> obligations =
            new ArrayList<Pair<TheoremProverObligation, TheoremProverObligation>>(this.newObligations.size());
        for(Pair<TheoremProverObligation, TheoremProverObligation> pair : this.newObligations) {

            Pair<TheoremProverObligation, TheoremProverObligation> p
                = new Pair<TheoremProverObligation, TheoremProverObligation>
                        (pair.x, pair.y);

            obligations.add(p);
        }

        return new ConditionalRewriteProof(obligations);
    }
}
