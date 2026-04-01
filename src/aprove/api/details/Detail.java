package aprove.api.details;

import java.util.*;

import aprove.api.prooftree.*;

/**
 * Contains a representation of a {@link ProofTreeNode} or {@link ProofTreeProof} that is understandable for the user.
 */
public interface Detail {

    Capability getCapability();

    Optional<String> getDetailString();
}
