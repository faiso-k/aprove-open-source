package aprove.verification.dpframework.DPProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class EDPProof extends Proof.DefaultProof {


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
        return CPFTag.AC_DP_PROOF;
    }

}
