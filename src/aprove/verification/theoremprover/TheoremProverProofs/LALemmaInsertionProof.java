package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Proof for LA lemma insertion
 *
 * @author dickmeis
 * @version $Id$
 *
 */

public class LALemmaInsertionProof extends TheoremProverProof {

    private Formula newFormula;
    private Formula constraint;
    private Formula lemma;
    private Formula speciallemma;
    private int newFormulaSize;

    public LALemmaInsertionProof(Formula newFormula, Formula constraint, Formula lemma, Formula speciallemma) {
        this.newFormula = newFormula;
        this.lemma = lemma;
        this.speciallemma = speciallemma;
        this.constraint = constraint;

        this.name      = "LA Lemma Insertion";
        this.shortName = "LA Lemma Insertion";
        this.longName  = "LA Lemma Insertion";

        this.newFormulaSize = newFormula.getSize();
    }

    /**
     * @return the newFormula
     */
    public Formula getNewFormula(){
        return this.newFormula;
    }

    public int getNewFormulaSize() {
        return this.newFormulaSize;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The new formula"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(this.newFormula.export(o));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.bold("was obtained by adding the instance "));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(this.speciallemma.export(o));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.bold(" of lemma "));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(this.lemma.export(o));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.bold(" to the subformula "));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(this.constraint.export(o) + ".");

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        return new LALemmaInsertionProof(this.newFormula.deepcopy(),
                this.constraint.deepcopy(), this.lemma.deepcopy(), this.speciallemma.deepcopy());
    }
}
