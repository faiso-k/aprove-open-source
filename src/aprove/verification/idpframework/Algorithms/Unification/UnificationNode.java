package aprove.verification.idpframework.Algorithms.Unification;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;

/**
 * A UnificationNode is a node in a UnificationDag representing a term. It is
 * linked with its fathers, children and equivalent nodes.
 * @author Martin Pluecker, copied from Matthias Sondermann
 * @version $Id$
 */
public class UnificationNode extends TermPairDagNode<UnificationNode> {

    /**
     * other nodes are equivalent to this if they have to be equal after
     * substitution
     */
    protected List<UnificationNode> equivNodes;
    /**
     * only for intern use of the unification algorithm
     */
    protected boolean completed;
    /**
     * only for intern use of the unification algorithm
     */
    protected UnificationNode pointer;
    /**
     * only for generating the mgu to prevent double evaluation
     */
    protected ITerm<?> substTerm;

    /**
     * A unification node is constructed with its term
     */
    public UnificationNode(final ITerm<?> term) {
        super(term);
        this.equivNodes = new ArrayList<UnificationNode>();
        this.completed = false;
        this.pointer = null;
        this.substTerm = null;
    }

    public void addEquivNode(final UnificationNode equivNode) {
        this.equivNodes.add(equivNode);
    }

    public boolean isCompleted() {
        return this.completed;
    }

    public void setCompleted(final boolean completed) {
        this.completed = completed;
    }

    public UnificationNode getPointer() {
        return this.pointer;
    }

    public void setPointer(final UnificationNode pointer) {
        this.pointer = pointer;
    }

    public List<UnificationNode> getEquivNodes() {
        return this.equivNodes;
    }

    public ITerm<?> getSubstTerm() {
        return this.substTerm;
    }

    public void setSubstTerm(final ITerm<?> substTerm) {
        this.substTerm = substTerm;
    }

    @Override
    public int hashCode() {
        return this.term.hashCode();
    }

    @Override
    public boolean equals(final Object other) {
        if (other == null) {
            return false;
        }
        if (this == other) {
            return true;
        }
        if (other instanceof UnificationNode) {
            final UnificationNode that = (UnificationNode) other;
            return this.getTerm().equals(that.getTerm());
        }
        return false;
    }
}