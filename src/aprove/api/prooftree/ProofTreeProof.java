package aprove.api.prooftree;

import java.util.*;

import aprove.api.details.*;

/**
 * Represents a proof in the {@link ProofTree}.
 */
public interface ProofTreeProof {

    Detail getDetail(Capability capability);

    String getName();

    Set<Capability> getCapabilities();

    String getImplication();
}
