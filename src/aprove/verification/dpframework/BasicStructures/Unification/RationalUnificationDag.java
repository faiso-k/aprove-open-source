package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Matthias Sondermann
 * @version $Id$
 */
public class RationalUnificationDag extends TermPairDag<RationalUnificationNode> {

    public RationalUnificationDag(final TRSTerm term1, final TRSTerm term2) {
        super(term1, term2, SharingMode.FULL);
    }

    @Override
    public RationalUnificationNode createNewNode(final TRSTerm term) {
        return new RationalUnificationNode(term);
    }

    /**
     * Adds an edge between node1 and node2 which represents the equivalence
     * between these two nodes or better between the terms which are
     * represented by the nodes. It is an undirected edge.
     * @result true iff both directions did not exist before
     */
    public boolean addEquivEdge(final RationalUnificationNode one, final RationalUnificationNode two) {
        return one.addEquivNode(two) & two.addEquivNode(one);
    }

    /**
     * Adds an equivalent edge between the two nodes representing the two
     * terms. The user has to check that these nodes exist. */
    public boolean addEquivEdge(final TRSTerm term1, final TRSTerm term2) {
        return this.addEquivEdge(this.termAtNode.get(term1), this.termAtNode.get(term2));
    }

    public Set<Pair<RationalUnificationNode, RationalUnificationNode>> getAllEquivalentNodes() {
        final Set<Pair<RationalUnificationNode, RationalUnificationNode>> returnSet =
            new LinkedHashSet<Pair<RationalUnificationNode, RationalUnificationNode>>();
        for (final RationalUnificationNode one : this.getNodes()) {
            for (final RationalUnificationNode two : one.getEquivNodes()) {
                returnSet.add(new Pair<RationalUnificationNode, RationalUnificationNode>(one, two));
            }
        }
        return returnSet;
    }

    /**
     * Adds additional edges (pointers and equivalence) to the dag
     */
    @Override
    public String toDOT() {
        final String linesep = System.getProperty("line.separator");
        final StringBuilder sb = new StringBuilder();
        // get "normal" graph
        sb.append(super.toDOT());
        // remove }
        sb.deleteCharAt(sb.length() - 2);
        // add pointers
        final Set<Set<RationalUnificationNode>> donePointers = new HashSet<Set<RationalUnificationNode>>();
        final Set<Set<RationalUnificationNode>> doneEquivs = new HashSet<Set<RationalUnificationNode>>();
        for (final RationalUnificationNode node : this.getNodes()) {
            if (node.getEquivalenceClass() != null) {
                final Set<RationalUnificationNode> setPointer = new HashSet<RationalUnificationNode>();
                setPointer.add(node);
                setPointer.add(node.getEquivalenceClass().getRepresentative());
                if (!donePointers.contains(setPointer)) {
                    sb.append("   " + node.getUniqueName() + " -> "
                        + node.getEquivalenceClass().getRepresentative().getUniqueName() + " [color=red];" + linesep);
                }
                donePointers.add(setPointer);
            }
            final Set<RationalUnificationNode> setEquiv = new HashSet<RationalUnificationNode>();
            for (final RationalUnificationNode eNode : node.getEquivNodes()) {
                setEquiv.add(node);
                setEquiv.add(eNode);
                if (!doneEquivs.contains(setEquiv)) {
                    sb.append("   " + node.getUniqueName() + " -> " + eNode.getUniqueName() + " [color=blue];"
                        + linesep);
                }
                doneEquivs.add(setEquiv);
            }
        }
        sb.append("}");
        return sb.toString();
    }
}
