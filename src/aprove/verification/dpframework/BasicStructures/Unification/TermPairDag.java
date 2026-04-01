package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * Basic implementation of a DAG which is able to represent a pair of terms
 * which possibly share some of their subexpressions.
 *
 * @author Matthias Sondermann
 * @version $Id$
 *
 * @param <N> The type of the node in the dag
 */
public abstract class TermPairDag<N extends TermPairDagNode<N>> implements DOT_Able {

    /**
     * mode info to create the dag
     */
    public enum SharingMode {
        FULL, VARIABLE,
    }

    /**
     * map between a term and a node which is reprenting it
     */
    protected Map<TRSTerm, N> termAtNode;
    /**
     * list of all nodes representing a function symbol in the dag
     */
    protected List<N> functionNodes;
    /**
     * list of all nodes representing a variable in the dag
     */
    protected List<N> variableNodes;
    /**
     * only needed for dot output
     */
    protected TRSTerm term1;
    protected TRSTerm term2;

    /**
     * Constructs a new dag out of the two terms
     */
    public TermPairDag(final TRSTerm term1, final TRSTerm term2, final SharingMode mode) {
        this.term1 = term1;
        this.term2 = term2;
        this.termAtNode = new HashMap<TRSTerm, N>();
        this.functionNodes = new ArrayList<N>();
        this.variableNodes = new ArrayList<N>();

        switch (mode) {
        case FULL:
            this.addTermWithFullSharing(term1, null);
            this.addTermWithFullSharing(term2, null);
            break;
        case VARIABLE:
            this.addTermWithVariableSharing(term1, null);
            this.addTermWithVariableSharing(term2, null);
            break;
        }
    }

    abstract N createNewNode(TRSTerm term);

    /**
     * Adds the term to the dag with full sharing, i.e. every common subexpression is shared
     * @param term To be added term
     * @param father Father node of the node representing the term
     */
    protected void addTermWithFullSharing(final TRSTerm term, final N father) {
        // remember if the term is in the dag
        // so that we don??t have to follow its children
        boolean isInDag = false;
        N actualNode = this.termAtNode.get(term);
        if (actualNode != null) {
            isInDag = true;
        }
        if (father != null && actualNode != null) {
            this.addDirectedEdge(father, actualNode);
        } else if (father == null && actualNode == null) {
            actualNode = this.createNewNode(term);
            this.addRootNodeToDag(actualNode);
        } else if (father != null && actualNode == null) {
            actualNode = this.createNewNode(term);
            this.addNodeToDag(actualNode, father);
        }
        //father == null && actualNode != null: do nothing

        // follow the children only if this term has not been included yet
        if (!term.isVariable() && !isInDag) {
            for (final TRSTerm term3 : ((TRSFunctionApplication) term).getArguments()) {
                this.addTermWithFullSharing(term3, actualNode);
            }
        }
    }

    protected void addTermWithVariableSharing(final TRSTerm term, final N father) {
        // term is a function application
        if (!term.isVariable()) {
            final N newNode = this.createNewNode(term);
            final TRSFunctionApplication func = (TRSFunctionApplication) term;

            // if the father is null this will be the rootnode
            if (father == null) {
                this.addRootNodeToDag(newNode);
            } else {
                this.addNodeToDag(newNode, father);
            }

            // add all subterms to the dag
            for (final TRSTerm child : func.getArguments()) {
                this.addTermWithVariableSharing(child, newNode);
            }
        }
        // term is a variable so we have to check if a node exists which represents this variable
        else {
            // check if there exists a term that represents the term
            final N node = this.termAtNode.get(term);

            if (node == null) {
                final N newNode = this.createNewNode(term);

                if (father == null) {
                    this.addRootNodeToDag(newNode);
                } else {
                    this.addNodeToDag(newNode, father);
                }
            } else {
                if (father != null) {
                    this.addDirectedEdge(father, node);
                }
            }
        }
    }

    protected void addNodeToDag(final N newNode, final N fatherNode) {
        this.addDirectedEdge(fatherNode, newNode);
        this.termAtNode.put(newNode.getTerm(), newNode);

        if (!newNode.getTerm().isVariable()) {
            this.functionNodes.add(newNode);
        } else {
            this.variableNodes.add(newNode);
        }
    }

    protected void addRootNodeToDag(final N rootNode) {
        this.termAtNode.put(rootNode.getTerm(), rootNode);
        if (!rootNode.getTerm().isVariable()) {
            this.functionNodes.add(rootNode);
        } else {
            this.variableNodes.add(rootNode);
        }
    }

    /**
     * Adds a directed edge from the father to its child
     */
    protected void addDirectedEdge(final N father, final N child) {
        father.addChild(child);
        child.addFather(father);
    }

    /**
     * @return Every node which represents a variable
     */
    public List<N> getVariableNodes() {
        return this.variableNodes;
    }

    /**
     * @return Every node which represents a function symbol
     */
    public List<N> getFunctionNodes() {
        return this.functionNodes;
    }

    /**
     * @return Every node
     */
    public List<N> getNodes() {
        final List<N> retList = new ArrayList<N>(this.functionNodes);
        retList.addAll(this.variableNodes);
        return retList;
    }

    /**
     * Please recognize that this method is implemented very stupid because it is only used for debugging up to now!
     * @return a string which can be used to create a dotty-graph
     */
    @Override
    public String toDOT() {
        final String linesep = System.getProperty("line.separator");
        final StringBuilder sb = new StringBuilder();
        sb.append("digraph DAG {" + linesep);
        for (final N node : this.getNodes()) {
            if (node.getTerm().equals(this.term1)) {
                sb.append("   " + node.getUniqueName() + " [label=\"" + node.toString() + "\", color=\"red\"];"
                    + linesep);
            } else if (node.getTerm().equals(this.term2)) {
                sb.append("   " + node.getUniqueName() + " [label=\"" + node.toString() + "\", color=\"green\"];"
                    + linesep);
            }
            sb.append("   " + node.getUniqueName() + " [label=\"" + node.toString() + "\"];" + linesep);
        }
        // counter for labeling the edges
        for (final N fatherNode : this.functionNodes) {
            for (int i = 0; i < fatherNode.getChildren().size(); i++) {
                final TermPairDagNode<N> childNode = fatherNode.getChildren().get(i);
                sb.append("   " + fatherNode.getUniqueName() + " -> " + childNode.getUniqueName() + " [label=\"" + i
                    + "\"];" + linesep);
            }
        }
        // If a term contains only one variable draw an extra node
        // (It does not matter if its already in the graph)
        if (this.term1.isVariable()) {
            sb.append("   " + this.termAtNode.get(this.term1).getUniqueName() + ";" + linesep);
        }
        if (this.term2.isVariable()) {
            sb.append("   " + this.termAtNode.get(this.term2).getUniqueName() + ";" + linesep);
        }
        sb.append("}" + linesep);
        return sb.toString();
    }
}
