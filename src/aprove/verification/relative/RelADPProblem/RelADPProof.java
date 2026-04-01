package aprove.verification.relative.RelADPProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

/**
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public abstract class RelADPProof extends Proof.DefaultProof {

    /**
     * toDOM is not supported for PDP-Proofs
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
        final Document doc,
        final Element childProof,
        final XMLMetaData xmlMetaData,
        final RelADPProblem radpp
    ) {
        return CPFTag.DP_NONTERMINATION_PROOF.create(
            doc,
            CPFTag.DP_RULE_REMOVAL.create(
                doc,
                CPFTag.adp(doc, xmlMetaData, radpp.getPAbs()),  // TODO: should these use CPFTag.trs?
                CPFTag.adp(doc, xmlMetaData, radpp.getPRel()),
                CPFTag.adp(doc, xmlMetaData, radpp.getQ().getR()),
                childProof
            )
        );
    }

}
