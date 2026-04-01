package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * A RationalUnificationNode is a node in a RationalUnificationDag representing
 * a term. It is linked with its fathers, children and equivalent
 * nodes and is probably member of an equivalence class
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
public class RationalUnificationNode extends TermPairDagNode<RationalUnificationNode> {

    /**
     * other nodes are equivalent to this if they have to be equal after substitution
     */
    private final Set<RationalUnificationNode> equivNodes;
    /**
     * only for intern use of the unification algorithm
     */
    private boolean completed;
    /**
     * only for intern use of the unification algorithm
     */
    private EquivalenceClass eClass;

    /**
     * a small helper for the equivalence class
     */

    /**
     * A unification node is constructed with its term
     */
    public RationalUnificationNode(final TRSTerm term) {
        super(term);
        this.equivNodes = new LinkedHashSet<RationalUnificationNode>();
        this.completed = false;
        this.eClass = null;
    }

    public void addToEquivalenceClass(final EquivalenceClass e) {
        this.eClass = e;
    }

    public EquivalenceClass getEquivalenceClass() {
        return this.eClass;
    }

    public boolean addEquivNode(final RationalUnificationNode equivNode) {
        return this.equivNodes.add(equivNode);
    }

    public boolean isCompleted() {
        return this.completed;
    }

    public void setCompleted(final boolean completed) {
        this.completed = completed;
    }

    public Set<RationalUnificationNode> getEquivNodes() {
        return this.equivNodes;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return this.term.hashCode();
    }

    /**
     * Nodes are equal iff the terms are equal
     * (This method does overwrite the super method because it is very
     * important that this equality holds!)
     */
    @Override
    public boolean equals(final Object other) {
        if (other == null) {
            return false;
        }
        if (this == other) {
            return true;
        }
        if (other instanceof RationalUnificationNode) {
            final RationalUnificationNode that = (RationalUnificationNode) other;
            return this.getTerm().equals(that.getTerm());
        }
        return false;
    }
}
