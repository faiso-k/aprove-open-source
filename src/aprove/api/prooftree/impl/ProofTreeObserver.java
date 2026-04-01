package aprove.api.prooftree.impl;

import java.util.*;
import java.util.function.*;

import aprove.prooftree.*;
import aprove.prooftree.Obligations.*;

public class ProofTreeObserver {

    private final BiConsumer<BasicObligationNode, ObligationNodeChild> proofHandler;
    private final BiConsumer<JunctorObligationNode, ObligationNode> childHandler;
    private final TruthValueListener truthValueListener;
    private final ChildAddListener childAddListener;

    public ProofTreeObserver(BiConsumer<BasicObligationNode, ObligationNodeChild> proofHandler,
                             BiConsumer<JunctorObligationNode, ObligationNode> childHandler,
                             TruthValueListener truthValueListener) {
        this.proofHandler = proofHandler;
        this.childHandler = childHandler;
        this.truthValueListener = truthValueListener;
        this.childAddListener = this::childAdded;
    }

    public void rootAdded(ObligationNode root) {
        nodeAppeared(root);
    }

    private void childAdded(BasicObligationNode basicNode, ObligationNodeChild child) {
        this.proofHandler.accept(basicNode, child);
        nodeAppeared(child.getNewObligation());
    }

    private void nodeAppeared(ObligationNode node) {
        node.addTruthValueListener(this.truthValueListener);

        if (node instanceof BasicObligationNode) {
            // Basic node: Watch for further children, but note all that already exist
            BasicObligationNode basicNode = (BasicObligationNode) node;
            Collection<ObligationNodeChild> currentChildren = basicNode.addChildAddListener(this.childAddListener);
            for (ObligationNodeChild child : currentChildren) {
                this.proofHandler.accept(basicNode, child);
                nodeAppeared(child.getNewObligation());
            }
        } else {
            // Junctor node: They don't change their children once they exist
            JunctorObligationNode junctorNode = (JunctorObligationNode) node;
            for (ObligationNode child : junctorNode.getChildren()) {
                this.childHandler.accept(junctorNode, child);
                nodeAppeared(child);
            }
        }
    }
}
