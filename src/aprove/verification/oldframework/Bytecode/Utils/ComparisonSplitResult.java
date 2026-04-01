package aprove.verification.oldframework.Bytecode.Utils;

import org.json.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * If we cannot refine the state to compute the result of some comparison, we
 * enforce the result using this SplitResult.
 *
 * @author Carsten Otto
 */
public class ComparisonSplitResult implements SplitResult {
    /**
     * The relation between to integers.
     */
    private final IntegerRelationType intRel;

    /**
     * Create a new SplitResult for a CMP opcode.
     * @param rel the result of evaluating the CMP opcode.
     */
    public ComparisonSplitResult(final IntegerRelationType rel) {
        this.intRel = rel;
    }

    /**
     * @return the the result of evaluating the CMP opcode.
     */
    public IntegerRelationType getCmpResult() {
        return this.intRel;
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
        sb.append("Comparison Split Result: " + this.intRel);
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Split Type", "Integer Comparison");
        res.put("Chosen Relation", this.intRel.toString());
        return res;
    }
}
