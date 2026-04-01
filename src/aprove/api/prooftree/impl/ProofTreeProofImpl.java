package aprove.api.prooftree.impl;

import java.util.*;

import aprove.api.details.*;
import aprove.api.details.impl.*;
import aprove.api.prooftree.*;
import aprove.prooftree.Proofs.*;

public class ProofTreeProofImpl implements ProofTreeProof {

    private final NodeDataContainer<Proof> proof;
    private final String implication;

    public ProofTreeProofImpl(NodeDataContainer<Proof> proof, String implication) {
        this.proof = proof;
        this.implication = implication;
    }

    @Override
    public Detail getDetail(Capability capability) {
        Objects.requireNonNull(capability);
        return Details.getDetail(capability, proof.getElement());
    }

    @Override
    public String getName() {
        return proof.getName();
    }

    @Override
    public Set<Capability> getCapabilities() {
        return proof.getCapabilities();
    }

    @Override
    public String getImplication() {
        return implication;
    }
}
