package aprove.verification.oldframework.Bytecode.Utils;

import org.json.*;

/**
 * If we cannot refine the state to compute the result of some comparison, we
 * enforce the result using this SplitResult.
 * @author Carsten Otto
 */
public class BooleanSplitResult implements SplitResult {
    /**
     * The truth value used for integer comparisons.
     */
    private final Boolean truth;

    /**
     * Create a new SplitResult for some integer comparison.
     * @param lastConditionTruthValueParam the result of the comparison
     */
    public BooleanSplitResult(final Boolean lastConditionTruthValueParam) {
        this.truth = lastConditionTruthValueParam;
    }

    /**
     * @return the boolean result of some integer comparison.
     */
    public Boolean getTruthValue() {
        return this.truth;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append("Boolean Split Result: " + this.truth);
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Split Type", "Bool");
        res.put("Truth Value", this.truth);
        return res;
    }
}
