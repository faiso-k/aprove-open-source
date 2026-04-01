package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Information to be written on the edges of the termination graph.
 * @author christian
 */
public class EdgeInformation extends ArrayList<VariableInformation> {
    /**
     * :)
     */
    private static final long serialVersionUID = 1L;

    protected EdgeInformation() {
        this(0);
    }

    private EdgeInformation(final int i) {
        super(i);
    }

    /**
     * @return the color used for this edge in DOT graphs.
     */
    public String getEdgeColor() {
        return "black";
    }

    /**
     * @return a string describing the format of the end node
     */
    public String getNodeFormat() {
        if (this.showFilled()) {
            return "color = " + this.getEdgeColor() + ", style=filled";
        }
        return "color = " + this.getEdgeColor();
    }

    /**
     * @return true iff the end node should be shown filled
     */
    public boolean showFilled() {
        return false;
    }

    public JSONObject toJSON() throws JSONException {
        throw new NotYetImplementedException("Not implemented yet.");
    }

    public void addLabelsToJSON(JSONObject res) throws JSONException {
        if (this.size() > 0) {
            final JSONArray labels = new JSONArray();
            for (VariableInformation e : this) {
                labels.put(e.toJSON());
            }
            res.put("Labels", labels);
        }
    }
}
