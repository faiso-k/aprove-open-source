package aprove.verification.dpframework.TRSProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class QTRSProof extends Proof.DefaultProof {


    /**
     * toDOM is no longer supported for DP-Proofs
     */
    @Override
    public final Element toDOM(final Document doc, final XMLMetaData storage) {
        return super.toDOM(doc, storage);
    }

    /**
     * delivers the tag that should be used for proofs
     */
    @Override
    final public CPFTag positiveTag() {
        return CPFTag.TRS_TERMINATION_PROOF;
    }

    /**
     * delivers the tag that should be used for disproofs
     */
    @Override
    final public CPFTag negativeTag() {
        return CPFTag.TRS_NONTERMINATION_PROOF;
    }

    protected Element ruleRemovalNontermProof(
            final Document doc, final Element childProof,
            final XMLMetaData xmlMetaData, final QTRSProblem newQTRS) {
        return CPFTag.TRS_NONTERMINATION_PROOF.create(doc,
                CPFTag.RULE_REMOVAL.create(doc,
                  CPFTag.trs(doc, xmlMetaData, newQTRS.getR()),
                  childProof));
    }

}
