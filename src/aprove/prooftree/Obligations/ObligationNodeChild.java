package aprove.prooftree.Obligations;

import aprove.prooftree.Proofs.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Convenience class to store a newly obtained obligation and the connection
 * to it.
 *
 * @author Marc Brockschmidt
 */
public class ObligationNodeChild {
    /**
     * The new obligation.
     */
    private final ObligationNode newObligation;

    /**
     * The proof leading to the new obligation.
     */
    private final Proof proof;

    /**
     * The implication of this proof.
     */
    private final Implication implication;

    /**
     * Time taken by processor.
     */
    private long consumedTime;

    /**
     * Create a new obligation node child.
     * @param newObl The new child obligation.
     * @param p The proof leading to <code>newObl</code>.
     * @param impl The implication of <code>p</code>.
     */
    public ObligationNodeChild(final ObligationNode newObl, final Proof p, final Implication impl) {
        this.newObligation = newObl;
        this.proof = p;
        this.implication = impl;
    }

    /**
     * @return the child
     */
    public ObligationNode getNewObligation() {
        return this.newObligation;
    }

    /**
     * @return the proof
     */
    public Proof getProof() {
        return this.proof;
    }

    /**
     * @return the implication
     */
    public Implication getImplication() {
        return this.implication;
    }

    /**
     * @return the consumedTime
     */
    public long getConsumedTime() {
        return this.consumedTime;
    }

    /**
     * @param consumedTime the consumedTime, used by Executor
     */
    public void setConsumedTime(final long consumedTime) {
        this.consumedTime = consumedTime;
    }
}
