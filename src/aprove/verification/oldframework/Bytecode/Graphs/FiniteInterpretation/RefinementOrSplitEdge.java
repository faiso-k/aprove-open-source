package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

/**
 * Just a common super class for refinements and splits.
 * @author cotto
 */
public abstract class RefinementOrSplitEdge extends EdgeInformation {

    /**
     * Some UID.
     */
    private static final long serialVersionUID = 923392915779863800L;

    /**
     * @return the label of this edge
     */
    public abstract String getLabel();

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean showFilled() {
        return true;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Type", "Refinement");
        super.addLabelsToJSON(res);
        return res;
    }
}
