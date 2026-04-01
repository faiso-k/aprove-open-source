package aprove.api;

import aprove.api.prooftree.*;

/**
 * This class represents a problem that can actually be analyzed.
 */
public interface AnalyzableProblemInput {

    ProofTreeBuilder newProofTreeBuilder();
}
