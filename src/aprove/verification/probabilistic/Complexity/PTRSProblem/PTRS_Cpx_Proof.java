package aprove.verification.probabilistic.Complexity.PTRSProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public abstract class PTRS_Cpx_Proof extends Proof.DefaultProof {

    /**
     * toDOM is not supported for probabilistic complexity proofs
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
        return CPFTag.PTRS_COMPLEXITY_PROOF;
    }

}
