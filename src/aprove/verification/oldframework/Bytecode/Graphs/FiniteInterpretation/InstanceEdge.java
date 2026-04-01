package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

/**
 * Representation of information about variables we gather when drawing an
 * instance edge.
 */
public class InstanceEdge extends EdgeInformation {

    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = -5313911770373894303L;

    /**
     * A string which is shown in the graph.
     */
    private final String label;

    /**
     * True iff this instantiation edge is created due to a proper merge
     */
    private final boolean fromMerge;

    /**
     * @param string a string which is used in the graph
     * @param fromMergeParam true iff this edge is created due to a proper merge
     */
    public InstanceEdge(final String string, final boolean fromMergeParam) {
        this.label = string;
        this.fromMerge = fromMergeParam;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        if (this.label != null) {
            return this.label;
        }
        return "instance";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#6599ff\"";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean showFilled() {
        return true;
    }

    /**
     * @return true iff this instantiation edge is created due to a proper merge
     */
    public boolean isFromMerge() {
        return this.fromMerge;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Type", "Instance");
        super.addLabelsToJSON(res);
        return res;
    }
}
