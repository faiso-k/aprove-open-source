package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * A unification dag is needed for the "Paterson-Wegman" unification
 * algorithm. The two to be unified terms are represented as 'trees'. But
 * because the two terms share their common subexpressions and so especially
 * their variables, the two trees 'merge' to a dag, a acyclic digraph.
 * For the unification only the variables have to be shared, but sharing
 * every common subexpression makes it faster.
 *
 * @author Matthias Sondermann
 * @veriosn $Id$
 */
public class UnificationDag extends TermPairDag<UnificationNode>{

    /** Constructs a new dag out of the two terms  */
    public UnificationDag(TRSTerm term1, TRSTerm term2) {
        super(term1, term2, SharingMode.FULL);
    }

    @Override
    public UnificationNode createNewNode(TRSTerm term) {
        return new UnificationNode(term);
    }

    /**
     * Adds an edge between node1 and node2 which represents the equivalence
     * between these two nodes or better between the terms which are
     * represented by the nodes. It??s an undirected edge.
     */
    public void addEquivEdge(UnificationNode node1, UnificationNode node2) {
        node1.addEquivNode(node2);
        node2.addEquivNode(node1);
    }

    /** Adds an equivalent edge between the two nodes representing the two
     * terms. The user has to check that these nodes exist. */
    public void addEquivEdge(TRSTerm term1, TRSTerm term2) {
        this.addEquivEdge(this.termAtNode.get(term1),this.termAtNode.get(term2));
    }

    /**
     * Adds additional edges (pointers and equivalence) to the dag
     */
    @Override
    public String toDOT() {
        String linesep = System.getProperty("line.separator");
        StringBuilder sb = new StringBuilder();
        // get "normal" graph
        sb.append(super.toDOT());
        // remove }
        sb.deleteCharAt(sb.length()-2);
        // add pointers
        Set<Set<UnificationNode>> donePointers = new HashSet<Set<UnificationNode>>();
        Set<Set<UnificationNode>> doneEquivs = new HashSet<Set<UnificationNode>>();
        for(UnificationNode node : this.getNodes()) {
            if(node.getPointer() != null) {
                Set<UnificationNode> setPointer = new HashSet<UnificationNode>();
                setPointer.add(node);
                setPointer.add(node.getPointer());
                if(!donePointers.contains(setPointer)) {
                    sb.append("   " + node.getUniqueName() + " -> " + node.getPointer().getUniqueName() + " [color=red];" + linesep);
                }
                donePointers.add(setPointer);
            }
            Set<UnificationNode> setEquiv = new HashSet<UnificationNode>();
            for(UnificationNode eNode : node.getEquivNodes()){
                setEquiv.add(node);
                setEquiv.add(eNode);
                if(!doneEquivs.contains(setEquiv)) {
                    sb.append("   " + node.getUniqueName() + " -> " + eNode.getUniqueName() + " [color=blue];" + linesep);
                }
                doneEquivs.add(setEquiv);
            }
        }
        sb.append("}");
        return sb.toString();
    }
}
