package aprove.api.prooftree.impl;

import java.util.*;

import org.stringtemplate.v4.compiler.STParser.*;

import aprove.api.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Logic.*;

public class ProofTreeImpl implements ProofTree {

    public static ProofTreeImpl from(ProofTreeListener listener, AProVE aprove) {
        ProofTreeOperationManagerImpl operationManager = new ProofTreeOperationManagerImpl(aprove);
        NodeTracker nodeTracker = new NodeTracker(operationManager);
        ProofTreeNodeImpl root = nodeTracker.createRoot(aprove.getRoot());
        return new ProofTreeImpl(listener, root, nodeTracker, operationManager);
    }

    private final ProofTreeListener listener;
    private final ProofTreeNodeImpl root;
    private final NodeTracker nodeTracker;

    private final ProofTreeOperationManagerImpl operationManager;

    public ProofTreeImpl(ProofTreeListener listener,
                         ProofTreeNodeImpl root,
                         NodeTracker nodeTracker,
                         ProofTreeOperationManagerImpl operationManager) {
        this.listener = listener;
        this.root = root;
        this.nodeTracker = nodeTracker;
        this.operationManager = operationManager;
    }

    @Override
    public ProofTreeNode getRoot() {
        return root;
    }

    @Override
    public ProofTreeOperationManager getOperationManager() {
        return operationManager;
    }

    @Override
    public void run(ProofResultHandler proofResultHandler) {
        Objects.requireNonNull(proofResultHandler);
        handleRoot();
        new ProofTreeObserver(this::handleProof,
                              this::handleChild,
                              this::handleTruthValue).rootAdded(root.getUnderlyingNode());
        if (Options.onlineCertification != null) {
            new OnlineCertificationObserver(this::handleCertificationResult).register((BasicObligationNode) root.getUnderlyingNode());
        }
        operationManager.runAprove(proofResultHandler);
    }

    private void handleRoot() {
        this.listener.createRoot(root);
    }

    private void handleChild(JunctorObligationNode parent, ObligationNode child) {
        this.listener.createChild(this.nodeTracker.createNode(parent, child));
        if (child.getTruthValue() != YNM.MAYBE) {
            handleTruthValue(child.getTruthValue(), child);
        }
    }

    private void handleProof(BasicObligationNode parent, ObligationNodeChild childContainer) {
        handleProof(parent,
                    childContainer.getNewObligation(),
                    childContainer.getImplication(),
                    childContainer.getProof());
    }

    private void handleProof(ObligationNode parent, ObligationNode child, Implication implication, Proof proof) {
        Implication impl =
                implication instanceof ComplexityImplication ? ((ComplexityImplication) implication).toAsymptotic()
                                                             : implication;
        this.listener.createProof(this.nodeTracker.createProofNode(parent, child, proof, impl));
        if (child.getTruthValue() != YNM.MAYBE) {
            handleTruthValue(child.getTruthValue(), child);
        }
    }

    private void handleTruthValue(TruthValue value, ObligationNode source) {
        if (value instanceof ComplexityYNM) {
            ComplexityYNM cvalue = (ComplexityYNM) value;
            String asymptotic = cvalue.discardConcreteValues().toString();
            String concrete = cvalue.toString();
            this.listener.setComplexity(this.nodeTracker.getNode(source), asymptotic, concrete);
        } else {
            this.listener.setTruth(this.nodeTracker.getNode(source), value.toString());
        }
    }

    private void handleCertificationResult(CPFCheckResult value, BasicObligationNode obligationNode) {
        this.listener.setCertificationState(this.nodeTracker.getNode(obligationNode), value);
    }
}
