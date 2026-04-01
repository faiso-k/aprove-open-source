package aprove.api.prooftree.impl;

import java.util.*;

import aprove.api.details.*;
import aprove.api.details.impl.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.*;

public class NodeDataContainer<T> {

    public static NodeDataContainer<Proof> fromProof(Proof proof) {
        return new NodeDataContainer<Proof>(proof,
                                            proof.getName(NameLength.SHORT),
                                            Details.getCapabilities(proof));
    }

    public static NodeDataContainer<ObligationNode> fromNode(ObligationNode node) {
        return new NodeDataContainer<ObligationNode>(node,
                                                     node.getRepresentation(),
                                                     Details.getCapabilities(node));
    }

    private final T element;
    private final String name;
    private final Set<Capability> capabilities;

    public NodeDataContainer(T element, String name, Set<Capability> capabilities) {
        this.element = element;
        this.name = name;
        this.capabilities = capabilities;
    }

    public T getElement() {
        return element;
    }

    public String getName() {
        return name;
    }

    public Set<Capability> getCapabilities() {
        return capabilities;
    }
}
