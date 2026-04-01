package aprove.api.prooftree;

/**
 * The proof tree contains information about each step of the analysis.
 * Use this class to run an analysis that provides live updates for each change to the proof tree.
 * This class is mainly used for the GUI, so the user gets feedback not only after the analysis is done, but right from the start of the analysis.
 */
public interface ProofTree {

    void run(ProofResultHandler proofResultHandler);

    ProofTreeNode getRoot();

    ProofTreeOperationManager getOperationManager();
}
