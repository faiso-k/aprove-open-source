/**
  * @author Marc Brockschmidt
  */

package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

/**
 * Representation of information about variables we gather when evaluating
 * a term. Most of this information ends up as variable constraints in the
 * final ITRS generated from the evaluation graph.
 */
public class EvaluationEdge extends EdgeInformation {
    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = 8479120166437088095L;

    @Override
    public String toString() {
        if (this.isEmpty()) {
            return "";
        }
        return super.toString();
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Type", "Evaluation");
        super.addLabelsToJSON(res);
        return res;
    }
}
