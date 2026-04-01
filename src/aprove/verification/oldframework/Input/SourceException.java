package aprove.verification.oldframework.Input;

import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Thrown when a translator is not able to construct a Program.
 *   @author Martin Mertens
 *   @version $Id$
 */

public class SourceException extends Exception {

    Proof proof;
    String name;

    public SourceException(String message, Proof proof, String name) {
        super(message);
        this.proof = proof;
        this.name = name;
    }

    public Proof getProof() {
        return this.proof;
    }

    public String getName() {
        return this.name;
    }

}
