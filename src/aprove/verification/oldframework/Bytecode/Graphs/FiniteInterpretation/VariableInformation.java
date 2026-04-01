package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

/**
 * @author christian
 *
 * Information regarding the relation of variables between states,
 * e.g. a4 < a5
 */
public interface VariableInformation {
    JSONObject toJSON() throws JSONException;
}
