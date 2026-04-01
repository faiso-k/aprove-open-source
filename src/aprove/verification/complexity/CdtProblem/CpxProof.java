package aprove.verification.complexity.CdtProblem;

import aprove.prooftree.Proofs.*;
import aprove.xml.*;

public abstract class CpxProof extends Proof.DefaultProof {

    /**
     * delivers the tag that should be used for proofs
     */
    @Override
    final public CPFTag positiveTag() {
        return CPFTag.COMPLEXITY_PROOF;
    }

}
