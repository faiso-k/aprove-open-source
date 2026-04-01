package aprove.api.prooftree;

import java.nio.file.*;
import java.util.*;

import aprove.api.details.*;

/**
 * Represents a node in the {@link ProofTree}.
 */
public interface ProofTreeNode {

    /**
     * Runs a sub analysis on this node.
     */
    void run(String userStrategyFragment, Timeout timeout, ProofResultHandler proofResultHandler);

    CertificationResult certify();

    void export(Path path) throws ExportFailedException;

    Detail getDetail(Capability capability);

    Optional<ProofTreeNode> getParent();

    String getName();

    Set<Capability> getCapabilities();

    Optional<ProofTreeProof> getProof();
}
