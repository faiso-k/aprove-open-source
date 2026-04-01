package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

/**
 * Edges that are only used to show debug information in the graph.
 * @author cotto
 */
public abstract class DebugEdge extends EdgeInformation {

    /**
     * Some UID.
     */
    private static final long serialVersionUID = -4084352586323905095L;

    /**
     * Possible label for this edge.
     */
    private final String label;

    public DebugEdge() {
        this.label = "";
    }

    /**
     * @param l Label for this edge
     */
    public DebugEdge(final String l) {
        this.label = l;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#ff0000\"";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.label;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Type", "Debug");
        super.addLabelsToJSON(res);
        return res;
    }
}
