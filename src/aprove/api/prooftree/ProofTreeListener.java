package aprove.api.prooftree;

/**
 * Implement this listener to receive live updates about each change to the {@link ProofTree}.
 */
public interface ProofTreeListener {

    void createRoot(ProofTreeNode node);

    void createChild(ProofTreeNode node);

    void createProof(ProofTreeNode node);

    void setTruth(ProofTreeNode node, String truth);

    void setComplexity(ProofTreeNode node, String asymptotic, String concrete);

    void setCertificationState(ProofTreeNode node, CPFCheckResult state);
}
