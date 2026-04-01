package aprove.verification.dpframework.TRSProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class CSRProof extends Proof.DefaultProof {

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
        final XMLMetaData xmlMetaData,
        final CSRProblem newCRS)
    {
        return CPFTag.TRS_NONTERMINATION_PROOF.create(doc,
                CPFTag.RULE_REMOVAL.create(doc,
 CPFTag.trs(doc, xmlMetaData, newCRS.getR()),
                  childProof));
    }

}
