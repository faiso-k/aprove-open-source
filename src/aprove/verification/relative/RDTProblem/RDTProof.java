package aprove.verification.relative.RDTProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

/**
 * @author Grigory Vartanyan
 * @version $Id$
 */
public abstract class RDTProof extends Proof.DefaultProof {

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

    protected Element ruleRemovalNontermProof(  // TODO: what is this, what is it used for?
        final Document doc,
        final Element childProof,
        final XMLMetaData xmlMetaData,
        final RDTProblem rdpp
    ) {
        return CPFTag.DP_NONTERMINATION_PROOF.create(doc);
    }

}
