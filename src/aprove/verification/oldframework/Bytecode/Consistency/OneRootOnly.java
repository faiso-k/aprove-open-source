package aprove.verification.oldframework.Bytecode.Consistency;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * @author christian
 * This class checks that there is only one node without predecessors
 */
public class OneRootOnly implements Checker {

    /**
    * The graph to be checked
    */
    private final MethodGraph graph;

    /**
     * If there is a root node (that is, one node without incoming edges),
     * this node is saved here. Otherwise, or if check wasn't called,
     * this is null.
     */
    private Node root1;

    /**
     * If there is more than node which is a root (as above), then
     * this is set to one of the two root nodes existing. Otherwise,
     * or if check wasn't called, this is null.
     */
    private Node root2;


    /**
     * @param g Graph to check
     */
    public OneRootOnly(final MethodGraph g) {
        this.root1 = null;
        this.root2 = null;
        this.graph = g;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Consistency.Checker#check()
     */
    @Override
    public boolean check() {
        this.graph.getGraphLock().readLock().lock();
        try {
            for (final Node n : this.graph.getNodes()) {
                if (!this.graph.hasPredecessor(n)) {
                    if (this.root1 == null) {
                        this.root1 = n;
                    } else {
                        this.root2 = n;
                        return false;
                    }
                }
            }
            return true;
        } finally {
            this.graph.getGraphLock().readLock().unlock();
        }
    }

    @Override
    public String toString() {
        if (this.root2 == null) {
            return "Check succeeded.";
        } else {
            return "Two roots found: \n" + this.root1 + "\n" + this.root2;
        }
    }

}
