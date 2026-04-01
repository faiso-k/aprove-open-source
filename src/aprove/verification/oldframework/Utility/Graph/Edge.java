package aprove.verification.oldframework.Utility.Graph;

import org.json.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * This class represents an edge of a graph, the attached object can freely be changed, it does not account for
 * equality.
 * @author Carsten Pelikan, cryingshadow
 * @version $Id$
 * @param <T> The label type.
 * @param <U> The type of the nodes.
 */
@SuppressWarnings({"deprecation"})
public class Edge<T,U> implements HTML_Able, java.io.Serializable, JSONExport {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -66840297053524523L;

    /**
     * The node where this edge ends at.
     */
    final Node<U> endNode;

    /**
     * An arbitrary object which is associated with this edge.
     */
    final T object;

    /**
     * The node where this edge starts from.
     */
    final Node<U> startNode;

    /**
     * Creates an edge without a label.
     * @param startNode The start node.
     * @param endNode The end node.
     */
    public Edge(Node<U> startNode, Node<U> endNode) {
        this(startNode, endNode, null);
    }

    /**
     * Creates an edge with the specified label.
     * @param startNode The start node.
     * @param endNode The end node.
     * @param object The label object.
     */
    public Edge(Node<U> startNode, Node<U> endNode, T object) {
        this.startNode = startNode;
        this.endNode = endNode;
        this.object = object;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof Edge) {
            Edge<?, ?> e = (Edge<?, ?>)o;
            return this.startNode.equals(e.startNode) && this.endNode.equals(e.endNode);
        }
        return false;

    }

    /**
     * @return The end node.
     */
    public Node<U> getEndNode() {
        return this.endNode;
    }

    /**
     * Returns the stored label object.
     * @return The label object which is stored in edge.
     */
    public T getObject() {
        return this.object;
    }

    /**
     * @return The start node.
     */
    public Node<U> getStartNode(){
        return this.startNode;
    }

    @Override
    public int hashCode() {
        return (this.startNode.hashCode() << 16) | (this.endNode.hashCode() & 0xffff);
    }

    @Override
    public String toHTML() {
        StringBuilder res = new StringBuilder();
        res.append("<TD align=center>");
        res.append(this.startNode.getNodeNumber());
        res.append("</TD><TD align=center>");
        if (this.object != null) {
            if (this.object.toString().equals(">")) {
                res.append("&gt;");
            } else if (this.object.toString().equals("=")) {
                res.append("="); //"&gt;=";
            } else {
                res.append(this.object.toString());
            }
        }
        res.append("</TD><TD align=center>");
        res.append(this.endNode.getNodeNumber());
        res.append("</TD>");
        return res.toString();
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("from", this.startNode.getNodeNumber());
        res.put("to", this.endNode.getNodeNumber());
        res.put("label", JSONExportUtil.toJSON(this.getObject()));
        return res;
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        if (this.object != null) {
            res.append("(");
            res.append(this.startNode);
            res.append(",");
            res.append(this.endNode);
            res.append(",");
            res.append(this.object);
            res.append(")");
        } else {
            res.append("(");
            res.append(this.startNode.getNodeNumber());
            res.append(" -> ");
            res.append(this.endNode.getNodeNumber());
            res.append(")");
        }
        return res.toString();
    }

}
