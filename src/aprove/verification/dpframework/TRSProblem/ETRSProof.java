package aprove.verification.dpframework.TRSProblem;

import org.w3c.dom.*;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class ETRSProof extends Proof.DefaultProof {


    /**
     * toDOM is no longer supported for ETRS-Proofs
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
        return CPFTag.AC_TERMINATION_PROOF;
    }

}
