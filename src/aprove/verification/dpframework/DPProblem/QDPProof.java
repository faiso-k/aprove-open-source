package aprove.verification.dpframework.DPProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class QDPProof extends Proof.DefaultProof {


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
        return CPFTag.DP_PROOF;
    }

    /**
     * delivers the tag that should be used for disproofs
     */
    @Override
    final public CPFTag negativeTag() {
        return CPFTag.DP_NONTERMINATION_PROOF;
    }

    protected Element ruleRemovalNontermProof(
            final Document doc, final Element childProof,
            final XMLMetaData xmlMetaData, final QDPProblem newQDP) {
        return CPFTag.DP_NONTERMINATION_PROOF.create(doc,
                CPFTag.DP_RULE_REMOVAL.create(doc,
                  CPFTag.dps(doc, xmlMetaData, newQDP.getP()),
                  CPFTag.trs(doc, xmlMetaData, newQDP.getR()),
                  childProof));
    }

}
