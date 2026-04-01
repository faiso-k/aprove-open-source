package aprove.verification.probabilistic.Termination.ADPProblem.AST;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public abstract class ADP_AST_Proof extends Proof.DefaultProof {

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

}
