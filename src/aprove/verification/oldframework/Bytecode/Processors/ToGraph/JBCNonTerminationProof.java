package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The proof that describes how we proved nontermination.
 * @author Marc Brockschmidt
 */
public class JBCNonTerminationProof extends DefaultProof {
    /** An example nontermination run. */
    private final NonTermWitness witness;

    /**
     * Create the proof.
     * @param w a witness for the nontermination
     */
    JBCNonTerminationProof(final NonTermWitness w) {
        super();
        this.witness = w;
        this.shortName = "JBCNonTerm";
        this.longName = "JBCNonTerminationProof";
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        return this.witness.export(o, level);
    }
}