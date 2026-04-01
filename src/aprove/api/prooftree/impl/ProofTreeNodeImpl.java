package aprove.api.prooftree.impl;

import java.nio.file.*;
import java.util.*;

import aprove.api.details.*;
import aprove.api.details.impl.*;
import aprove.api.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

public class ProofTreeNodeImpl implements ProofTreeNode {

    private final ProofTreeOperationManagerImpl operationManager;
    private final Optional<ProofTreeNodeImpl> parent;
    private final NodeDataContainer<ObligationNode> node;
    private final Optional<ProofTreeProofImpl> proof;

    public ProofTreeNodeImpl(ProofTreeOperationManagerImpl operationManager,
                             Optional<ProofTreeNodeImpl> parent,
                             NodeDataContainer<ObligationNode> node,
                             Optional<ProofTreeProofImpl> proof) {
        this.operationManager = operationManager;
        this.parent = parent;
        this.node = node;
        this.proof = proof;
    }

    @Override
    public void run(String userStrategyFragment, Timeout timeout, ProofResultHandler proofResultHandler) {
        Objects.requireNonNull(userStrategyFragment);
        Objects.requireNonNull(timeout);
        Objects.requireNonNull(proofResultHandler);
        UserStrategy userStrategy = StrategyTranslator.strategyFragment(userStrategyFragment);
        List<BasicObligationNode> nodes = ControllerUtils.collectBasicObligationNodes(node.getElement());
        operationManager.runSubAprove(nodes, userStrategy, timeout, proofResultHandler);
    }

    @Override
    public CertificationResult certify() {
        return CertificationHandler.certify(node.getElement());
    }

    @Override
    public void export(Path path) throws ExportFailedException {
        Objects.requireNonNull(path);
        try {
            ExportHandler.export(node.getElement(), path);
        } catch (Exception e) {
            throw new ExportFailedException(e);
        }
    }

    @Override
    public Detail getDetail(Capability capability) {
        Objects.requireNonNull(capability);
        return Details.getDetail(capability, node.getElement());
    }

    @Override
    public Optional<ProofTreeNode> getParent() {
        return parent.map(p -> p);
    }

    @Override
    public String getName() {
        return node.getName();
    }

    @Override
    public Set<Capability> getCapabilities() {
        return node.getCapabilities();
    }

    @Override
    public Optional<ProofTreeProof> getProof() {
        return proof.map(p -> p);
    }

    public ObligationNode getUnderlyingNode() {
        return node.getElement();
    }
}
