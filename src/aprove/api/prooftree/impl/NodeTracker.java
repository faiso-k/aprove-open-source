package aprove.api.prooftree.impl;

import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.oldframework.Logic.*;

public class NodeTracker {

    private final ConcurrentMap<ObligationNode, ProofTreeNodeImpl> underlyingToApi = new ConcurrentHashMap<>();
    private final ProofTreeOperationManagerImpl operationManager;

    public NodeTracker(ProofTreeOperationManagerImpl operationManager) {
        this.operationManager = operationManager;
    }

    public ProofTreeNodeImpl createProofNode(ObligationNode parent,
                                             ObligationNode node,
                                             Proof proof,
                                             Implication implication) {
        return createNode(Optional.of(getNode(parent)),
                          NodeDataContainer.fromNode(node),
                          Optional.of(new ProofTreeProofImpl(NodeDataContainer.fromProof(proof),
                                                             implication.toString())));
    }

    public ProofTreeNodeImpl createNode(ObligationNode parent, ObligationNode node) {
        return createNode(Optional.of(getNode(parent)), NodeDataContainer.fromNode(node), Optional.empty());
    }

    public ProofTreeNodeImpl createRoot(ObligationNode node) {
        return createNode(Optional.empty(), NodeDataContainer.fromNode(node), Optional.empty());
    }

    private ProofTreeNodeImpl createNode(Optional<ProofTreeNodeImpl> parent,
                                         NodeDataContainer<ObligationNode> node,
                                         Optional<ProofTreeProofImpl> proof) {
        ProofTreeNodeImpl result = new ProofTreeNodeImpl(operationManager, parent, node, proof);
        ProofTreeNodeImpl old = this.underlyingToApi.put(result.getUnderlyingNode(), result);
        if (old != null) {
            throw new IllegalArgumentException("Duplicate node!");
        }
        return result;
    }

    public ProofTreeNodeImpl getNode(ObligationNode node) {
        return this.underlyingToApi.get(node);
    }
}
