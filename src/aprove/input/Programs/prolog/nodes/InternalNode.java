package aprove.input.Programs.prolog.nodes;

import java.util.*;

/**
 * Abstract superclass for internal syntax tree nodes.<br><br>
 *
 * Created: May 5, 2006<br>
 * Last modified: Oct 18, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class InternalNode {

    private String text;
    private int line, pos;

//---------------- constructors ----------------

    /**
     * Constructs a new InternalNode with the specified text.
     * @param text The node's text.
     */
    public InternalNode(String text, int line, int pos) {
        this.text = text;
        this.line = line;
        this.pos = pos;
    }

//--------------- public methods --------------------

    /**
     * Adds a specified child node after a specified father node in the
     * syntax tree with this InternalNode as root node. If the father
     * node does not exist in this syntax tree, the method will not do
     * anything and return false. Otherwise the child node is added and
     * the method returns true.
     * @param parent The father node, after which the child node should
     *               be added.
     * @param child The node to add.
     * @return True, if the child node could be added successfully.
     *         False otherwise.
     */
    public boolean addAfter (InternalNode parent, InternalNode child) {
        if (parent == null || parent.equals(this)) {
            return this.addChild(child);
        } else {
            List<InternalNode> children = this.getChildren();
            if (children != null) {
                for (InternalNode node : children) {
                    if (node.addAfter(parent,child)) {
                        return true;
                    }
                }
            }
            return false;
        }
    }

    /**
     * Adds the specified InternalNode to the children of this
     * InternalNode. If the child could successfully be added, this
     * method returns true. Otherwise it returns false.
     * @param child The InternalNode to add.
     * @return True, if the child could successfully be added.
     *         False otherwise.
     */
    public abstract boolean addChild (InternalNode child);

    /**
     * Applies a TreeWalker on the syntax tree with this InternalNode as
     * root node. The traversal of the tree is a depth first search, but
     * the TreeWalker's action is performed at the last time a node is
     * visited.
     * @param walker The TreeWalker to apply.
     */
    public void apply (TreeWalker walker) {
        List<InternalNode> children = this.getChildren();
        if (children != null) {
            for (InternalNode node : children) {
                node.apply(walker);
            }
        }
        walker.action(this);
    }

    /**
     * Applies a TreeWalker on the syntax tree with this InternalNode as
     * root node. The traversal of the tree is a depth first search, but
     * the TreeWalker's action is performed every first time a node is
     * visited.
     * @param walker The TreeWalker to apply.
     */
    public void applyFirst (TreeWalker walker) {
        walker.action(this);
        List<InternalNode> children = this.getChildren();
        if (children != null) {
            for (InternalNode node : children) {
                node.applyFirst(walker);
            }
        }
    }

    /**
     * Returns the InternalNode's children.
     * @return The InternalNode's children.
     */
    public abstract List<InternalNode> getChildren();

    /**
     * Returns the line of this node's text in the original program.
     * @return The line of this node's text in the original program.
     */
    public int getLine() {
        return this.line;
    }

    /**
     * Returns the column of this node's text in the original program.
     * @return The column of this node's text in the original program.
     */
    public int getPos() {
        return this.pos;
    }

    /**
     * Returns the InternalNode's text.
     * @return The InternalNode's text.
     */
    public String getText() {
        return this.text;
    }

    /**
     * Sets the InternalNode's text.
     * @param text The new text for this InternalNode.
     */
    public void setText(String text) {
        this.text = text;
    }

    /**
     * Shows the syntax tree with this InternalNode as root node as a
     * dotty graph.
     */
    public void showDotty () {
        StringBuffer dot = new StringBuffer(),
                     nodes = new StringBuffer(),
                     edges = new StringBuffer();
        Map<InternalNode,Integer> uniqueMap = new LinkedHashMap<InternalNode,Integer>();
        Counter counter = new Counter();
        this.collectInfo(nodes,edges,counter,uniqueMap,0);
        dot.append("digraph DAG {\n");
        dot.append("   1" + " [label=\"number of nodes: " + counter.get() + "\", color=\"red\"];\n");
        dot.append(nodes);
        dot.append(edges);
        dot.append("}");
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString () {
        return this.toString("");
    }

//------------------ private methods --------------------

    /**
     * Helper method to build the dotty String.
     */
    private void collectInfo (StringBuffer nodes, StringBuffer edges, Counter c, Map<InternalNode,Integer> uniqueMap, int parent) {
        int thisNumber = c.get();
        c.plus();
        uniqueMap.put(this, thisNumber);
        if (parent == 0) {
            List<InternalNode> children = this.getChildren();
            if (children != null) {
                for (InternalNode child : children) {
                    child.collectInfo(nodes,edges,c,uniqueMap,thisNumber);
                }
            }
            return;
        }
        nodes.append("   " + thisNumber + " [label=\"" + this.getText(this) + "\", color=\"red\"];\n");
        edges.append("   " + parent + " -> " + thisNumber + "\n");
        List<InternalNode> children = this.getChildren();
        if (children != null) {
            for (InternalNode child : children) {
                child.collectInfo(nodes,edges,c,uniqueMap,thisNumber);
            }
        }
    }

    /**
     * Helper method to format the representation of InternalNodes in the
     * dotty graph.
     * @param node The node to represent.
     * @return A String representation of the specified node for the
     *         dotty graph.
     */
    private String getText(InternalNode node) {
        String text = node.getClass().getSimpleName();
        text += ": " + this.getText();
        text = text.replace("\"", "\\\"");
        text = text.replace("\n", "\\n");
        return text;
    }

    /**
     * Helper method to inline the general String representation of
     * InternalNodes for the toString() method.
     * @param prefix The leading white space.
     * @return The inlined String representation of this InternalNode.
     */
    private String toString (String prefix) {
        String res = prefix + this.text + "\n";
        List<InternalNode> children = this.getChildren();
        if (children != null) {
            for (InternalNode child : children) {
                res += child.toString(prefix + "      ");
            }
        }
        return res;
    }

//------------- private classes ------------------

    /**
     * Wrapper class for a simple counter.<br><br>
     *
     * Created: May 5, 2006<br>
     * Last modified: Oct 18, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private class Counter {

        private int i;

        /**
         * Constructs a new Counter with initial value 1.
         */
        private Counter () {
            this.i = 1;
        }

        /**
         * Returns the counter's value.
         * @return The counter's value.
         */
        private int get () {
            return this.i;
        }

        /**
         * Increases the counter.
         */
        private void plus () {
            this.i++;
        }

    }

}
