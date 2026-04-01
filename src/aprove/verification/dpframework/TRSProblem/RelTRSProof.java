package aprove.verification.dpframework.TRSProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class RelTRSProof extends Proof.DefaultProof {

    /**
     * delivers the tag that should be used for proofs
     */
    @Override
    final public CPFTag positiveTag() {
        return CPFTag.RELATIVE_TERMINATION_PROOF;
    }

    /**
     * delivers the tag that should be used for disproofs
     */
    @Override
    final public CPFTag negativeTag() {
        return CPFTag.RELATIVE_NONTERMINATION_PROOF;
    }

    protected Element ruleRemovalNontermProof(
            final Document doc, final Element childProof,
            final XMLMetaData xmlMetaData, final RelTRSProblem newRelTRS) {
        return CPFTag.RELATIVE_NONTERMINATION_PROOF.create(doc,
                CPFTag.RULE_REMOVAL.create(doc,
                  CPFTag.trs(doc, xmlMetaData, newRelTRS.getR()),
                  CPFTag.trs(doc, xmlMetaData, newRelTRS.getS()),
                  childProof));
    }

}
