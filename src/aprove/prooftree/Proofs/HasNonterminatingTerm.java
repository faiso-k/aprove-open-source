package aprove.prooftree.Proofs;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Implemented by objects which have a non-terminating term. Typically,
 * such objects are proofs, proof trees, ...
 * @author fuhs
 */
public interface HasNonterminatingTerm {

    /**
     * @return A non-terminating start term as a witness for non-termination, null if no such term could be retrieved
     *         (in a sound way) from the underlying proof tree (in particular, this is the case if the initial
     *         obligation is not a term rewrite system).
     */
    TRSTerm getNonterminatingTerm();

}
