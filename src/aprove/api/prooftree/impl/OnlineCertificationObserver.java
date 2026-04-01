package aprove.api.prooftree.impl;

import aprove.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.CPF.*;

public class OnlineCertificationObserver {

    private final OnlineCertificationListener certificationResultHandler;
    private final ChildAddListener childAddListener;

    public OnlineCertificationObserver(OnlineCertificationListener certificationResultHandler) {
        this.certificationResultHandler = certificationResultHandler;
        this.childAddListener = this::childAdded;
    }

    private void childAdded(BasicObligationNode basicNode, ObligationNodeChild child) {
        childAdded(child.getNewObligation());
    }

    private void childAdded(ObligationNode node) {
        if (node instanceof BasicObligationNode) {
            BasicObligationNode basicNode = (BasicObligationNode) node;
            register(basicNode);
        } else {
            JunctorObligationNode junctorNode = (JunctorObligationNode) node;
            for (ObligationNode child : junctorNode.getChildren()) {
                childAdded(child);
            }
        }
    }

    public void register(BasicObligationNode basicNode) {
        basicNode.addChildAddListener(this.childAddListener);
        basicNode.addOnlineCertificationListener(this.certificationResultHandler);
    }
}
