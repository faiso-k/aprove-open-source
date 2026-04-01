package aprove.verification.oldframework.Bytecode.Utils;

import org.json.*;

/**
 * Implementing getPrimitiveClass would need information about a String
 * content. As the number of differently handled cases is quite finite,
 * we just do a split. This convenience class holds the split result.
 *
 * @author Marc Brockschmidt
 */
public class GetPrimitiveClassSplitResult implements SplitResult {
    /**
     * The primitive type class chosen by this result.
     */
    private final FuzzyPrimitiveType chosenPrimitiveType;

    /**
     * Create a new SplitResult for a getPrimitiveClass call.
     * @param chosenPrimTypeClass the chosen primitive type class
     */
    public GetPrimitiveClassSplitResult(final FuzzyPrimitiveType chosenPrimType) {
        this.chosenPrimitiveType = chosenPrimType;
    }

    /**
     * @return the chosen primitive type
     */
    public FuzzyPrimitiveType getChosenPrimType() {
        return this.chosenPrimitiveType;
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
        sb.append("getPrimitiveClass Split Result: " + this.chosenPrimitiveType);
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Split Type", "Primitive Class");
        res.put("Chosen Primitive Type", this.chosenPrimitiveType.toBinaryName());
        return res;
    }
}