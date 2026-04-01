package aprove.verification.oldframework.Utility.Graph;

import java.util.concurrent.atomic.*;

/**
 * This class represents a node in a graph.
 * Nodes are identified and compared by their unique number,
 * the attached object is irrelevant for comparison.
 * @author Carsten Pelikan, Peter Schneider-Kamp
 * @version $Id$
 * @param <T> The type of the node contents.
 */
public class Node<T> implements Comparable<Node<?>>, java.io.Serializable, PrettyStringable {

    /**
     * The next free id number.
     */
    private static AtomicInteger nextNodeNumber = new AtomicInteger(1);

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 4856666530209175320L;

    /**
     * An user object associated with this node.
     */
    T object;

    /**
     * An unique id number for this node.
     */
    private final int nodeNumber;

    /**
     * Creates a node without an associated user object.
     */
    public Node() {
        this(null);
    }

    /**
     * Creates a node with a given user object.
     * @param object An object to associate with this node.
     */
    public Node(final T object) {
        this.object = object;
        this.nodeNumber = Node.nextNodeNumber.getAndIncrement();
    }


    /* (non-Javadoc)
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(final Node<?> n) {
        return this.nodeNumber - n.nodeNumber;
    }


    /**
     * Returns the unique id for this node.
     * @return The unique id for this node.
     */
    public int getNodeNumber() {
        return this.nodeNumber;
    }

    /**
     * @return The object that this node contains.
     */
    public T getObject() {
        return this.object;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Graph.PrettyStringable#prettyToString()
     */
    @Override
    public String prettyToString() {
        String temp = this.nodeNumber + "";
        if (this.object != null) {
            temp = temp + ": " + (this.object instanceof PrettyStringable ? ((PrettyStringable)this.object).prettyToString() : this.object.toString());
        }
        return temp;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        String temp = this.nodeNumber+"";
        if (this.object != null) {
            temp = temp + ": "+this.object.toString();
        }
        return temp;
    }
    
    
    //Explicitly forces this to behave like the default implementation in Object class
    @Override
    public boolean equals(Object obj) {
    	return this == obj;
    }
    
  //Explicitly forces this to behave like the default implementation in Object class
    @Override
    public int hashCode() {
    	return System.identityHashCode(this);
    }

    //    protected String getTikZLabel() {
    //        if (this.getObject() instanceof TikZLabelable) {
    //            return ((TikZLabelable) this.getObject()).toTikZLabel();
    //        }
    //
    //        String text = this.getObject().toString();
    //
    //        int start = 0;
    //        final int length = text.length();
    //
    //        int index;
    //
    //        while (start < length && (index = text.substring(start, length).indexOf('_')) >= 0) {
    //            text = text.substring(start, index) + "\\" + text.substring(index, length);
    //            start = index + 2;
    //        }
    //
    //        return "\\texttt{" + text + "}";
    //    }
    //
    //    protected String getTikZNodeID() {
    //        return "(" + this.getNodeNumber() + ")";
    //    }

}
