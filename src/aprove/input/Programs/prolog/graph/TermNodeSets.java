package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author cryingshadow
 * Contains all relevant nodes in a derivation graph for termination analysis.
 */
public class TermNodeSets {

    /**
     * Contains all successors of instance or generalization nodes.
     */
    private final Set<Node<PrologAbstractState>> instanceChildren;

    /**
     * Contains all instance and generalization nodes.
     */
    private final Set<Node<PrologAbstractState>> instanceNodes;

    /**
     * Contains all split nodes.
     */
    private final Set<Node<PrologAbstractState>> splitNodes;

    /**
     * Contains all success nodes.
     */
    private final Set<Node<PrologAbstractState>> successNodes;

    /**
     * Standard constructor.
     * @param iNodes The instance and generalization nodes.
     * @param succNodes The success nodes.
     * @param splNodes The split nodes.
     * @param iChildren The successors of instance or generalization nodes.
     */
    public TermNodeSets(
        final Set<Node<PrologAbstractState>> iNodes,
        final Set<Node<PrologAbstractState>> succNodes,
        final Set<Node<PrologAbstractState>> splNodes,
        final Set<Node<PrologAbstractState>> iChildren)
    {
        this.instanceNodes = iNodes;
        this.successNodes = succNodes;
        this.splitNodes = splNodes;
        this.instanceChildren = iChildren;
    }

    /**
     * Returns the successors of instance or generalization nodes.
     * @return The successors of instance or generalization nodes.
     */
    public Set<Node<PrologAbstractState>> getInstanceChildren() {
        return this.instanceChildren;
    }

    /**
     * Returns the instance and generalization nodes.
     * @return The instance and generalization nodes.
     */
    public Set<Node<PrologAbstractState>> getInstanceNodes() {
        return this.instanceNodes;
    }

    /**
     * Returns the split nodes.
     * @return The split nodes.
     */
    public Set<Node<PrologAbstractState>> getSplitNodes() {
        return this.splitNodes;
    }

    /**
     * Returns the success nodes.
     * @return The success nodes.
     */
    public Set<Node<PrologAbstractState>> getSuccessNodes() {
        return this.successNodes;
    }

}
