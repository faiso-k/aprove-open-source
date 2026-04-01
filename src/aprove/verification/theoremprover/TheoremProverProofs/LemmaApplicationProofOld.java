package aprove.verification.theoremprover.TheoremProverProofs;

/**
 * This proof collects information about a lemma application.
 *
 * This file was developed ongoing from LemmaApplicationProof in revision 1.9.
 *
 * @author dickmeis
 * @version $Id$
 */

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class LemmaApplicationProofOld extends TheoremProverProof {

    protected TheoremProverObligation newObligation;

    protected Set<Formula> lemmasUsed;

    public LemmaApplicationProofOld() {
    }

    public LemmaApplicationProofOld(TheoremProverObligation newObligation, Set<Formula> lemmasUsed) {
        super();

        this.name = "Lemma Application";
        this.shortName = this.name;
        this.longName  = this.name;

        this.lemmasUsed = lemmasUsed;
        this.newObligation = newObligation;
    }

    @Override
    public String export(Export_Util o) {
        if (Proof.CACHE_VALUES) {
                if (this.result.length() != 0) {
                    return this.result.toString();
                }
        } else {
            this.startUp();
        }

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The formula could be reduced by lemma application to the following new obligation:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation));
        stringBuffer.append(o.paragraph());


        if (this.lemmasUsed.size()==1){
            stringBuffer.append(o.bold("using the following lemma:"));
        }
        else{
            stringBuffer.append(o.bold("using the following lemmas:"));
        }

        stringBuffer.append(o.linebreak());

        for(Formula formula : this.lemmasUsed) {
            stringBuffer.append(o.export(formula));
            stringBuffer.append(o.linebreak());
        }

        return stringBuffer.toString();
    }

    public String toBibTeX() {
        return null;
    }

    @Override
    public Proof deepcopy() {

        Set<Formula>  lemmasUsed = new LinkedHashSet<Formula>();
        for(Formula formula : this.lemmasUsed) {
            lemmasUsed.add(formula.deepcopy());
        }

        return new LemmaApplicationProofOld(this.newObligation.deepcopy(), lemmasUsed);
    }

}
