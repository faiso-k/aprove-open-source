package aprove.prooftree;

import aprove.prooftree.Obligations.*;

/**
 * Interface implemented by all classes waiting for new nodes in a proof
 * tree.
 */
public interface ChildAddListener {
    /**
     * Method invoked in the proof tree expansion whenever a new obligation
     * node is added.
     *
     * @param source obligation node for which a new child was added.
     * @param child a triple of the new obligation, the non-termination
     *  implication and the proof leading from the old to the new
     *  obligation.
     */
    void childAdded(BasicObligationNode source, ObligationNodeChild child);
}
