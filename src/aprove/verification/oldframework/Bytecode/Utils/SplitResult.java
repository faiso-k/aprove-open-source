package aprove.verification.oldframework.Bytecode.Utils;

import org.json.*;

/**
 * If we cannot refine the state to compute the result of some comparison, we
 * enforce the result using this SplitResult.
 * @author Carsten Otto
 */
public interface SplitResult {
    /**
     * Append a string representation of this instance to <code>sb</code>
     * @param sb some StringBuilder
     */
    void toString(final StringBuilder sb);

    /**
     * @return JSON representation of the split result.
     * @throws JSONException
     */
    JSONObject toJSON() throws JSONException;
}
