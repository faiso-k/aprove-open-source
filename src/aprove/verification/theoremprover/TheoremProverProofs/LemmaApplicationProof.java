package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.LemmaApplication.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * This proof collects information about a lemma application.
 */
public class LemmaApplicationProof extends TheoremProverProof {

    protected ArrayList<LemmaApplicationResult> lemmaApplicationResults;

    public LemmaApplicationProof() {
    }

    public LemmaApplicationProof(final ArrayList<LemmaApplicationResult> lemmaApplicationResult) {
        super();

        this.name = "Lemma Application";
        this.shortName = this.name;
        this.longName = this.name;

        this.lemmaApplicationResults = lemmaApplicationResult;
    }

    @Override
    public String export(final Export_Util o) {
        if (Proof.CACHE_VALUES) {
            if (this.result.length() != 0) {
                return this.result.toString();
            }
        } else {
            this.startUp();
        }

        final StringBuffer stringBuffer = new StringBuffer();

        if (this.lemmaApplicationResults.size() == 1) {
            stringBuffer.append(o.bold("The formula could be reduced by lemma application to the following new obligation:"));
        } else {
            stringBuffer.append(o.bold("The formula could be reduced by lemma application to the following new obligations:"));
        }
        stringBuffer.append(o.paragraph());

        for (final LemmaApplicationResult lemmaApplicationResult : this.lemmaApplicationResults) {
            stringBuffer.append(o.export(lemmaApplicationResult.getResult()));
            stringBuffer.append(o.linebreak());

            stringBuffer.append(o.bold("using the following lemma:"));
            stringBuffer.append(o.linebreak());

            stringBuffer.append(o.export(lemmaApplicationResult.getLemma()) + " was applied "
                + lemmaApplicationResult.getDirection() + " at position " + lemmaApplicationResult.getPosition());
            if (Globals.DEBUG_DICKMEIS) {
                stringBuffer.append(" having utility measure " + lemmaApplicationResult.getUtilityEstimation());
            }

            stringBuffer.append(o.linebreak());

            stringBuffer.append(o.paragraph());
        }

        return stringBuffer.toString();
    }

    public String toBibTeX() {
        return null;
    }

    @Override
    public Proof deepcopy() {

        final ArrayList<LemmaApplicationResult> newLemmaApplicationResults = new ArrayList<LemmaApplicationResult>();

        for (final LemmaApplicationResult result : this.lemmaApplicationResults) {
            newLemmaApplicationResults.add(result.deepcopy());
        }

        return new LemmaApplicationProof(newLemmaApplicationResults);
    }

}
