package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Proof for LA lemma just insertion
 *
 * @author dickmeis
 * @version $Id$
 *
 */

public class LALemmaJustInsertionProof extends TheoremProverProof {

    private List<Formula> lemmas;
    private Set<AlgebraTerm> multiplicants;

    public LALemmaJustInsertionProof() {
    }

    public LALemmaJustInsertionProof(Set<AlgebraTerm> multiplicants, List<Formula> lemmas) {
        this.multiplicants = multiplicants;
        this.lemmas = lemmas;

        this.name      = "LA Lemma Just Insertion";
        this.shortName = "LA Lemma Just Insertion";
        this.longName  = "LA Lemma Just Insertion";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("Because of the terms:"));
        stringBuffer.append(o.newline());
        stringBuffer.append(o.set(this.multiplicants, 3));

        stringBuffer.append(o.bold("the following instances of lemmas might be helpful:"));
        stringBuffer.append(o.newline());
        stringBuffer.append(o.set(this.lemmas, 3));
        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        Set<AlgebraTerm> newMultiplicants = new HashSet<AlgebraTerm>(this.multiplicants.size());
        for(AlgebraTerm multiplicant : this.multiplicants) {
            newMultiplicants.add(multiplicant.deepcopy());
        }

        List<Formula> newLemmas = new ArrayList<Formula>(this.lemmas.size());
        for(Formula formula : this.lemmas) {
            newLemmas.add(formula.deepcopy());
        }

        return new LALemmaJustInsertionProof(newMultiplicants, newLemmas);
    }
}
