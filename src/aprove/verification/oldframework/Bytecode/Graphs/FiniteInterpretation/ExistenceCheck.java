package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Label indicating that we checked for the non-nullness of an object.
 *
 * @author Marc Brockschmidt
 */
public class ExistenceCheck implements ObjectInformation {
    /** The reference checked for nullness. */
    private final AbstractVariableReference ref;
    /** Whether the reference was NULL or not. */
    private final boolean exists;

    /**
     * @param r The reference checked for nullness.
     * @param exists Whether the reference was NULL or not.
     */
    public ExistenceCheck(final AbstractVariableReference r, final boolean exists) {
        super();
        this.ref = r;
        this.exists = exists;
    }

    /**
     * @return the reference checked for nullness.
     */
    @Override
    public AbstractVariableReference getRef() {
        return this.ref;
    }

    /**
     * @return whether the reference was NULL or not.
     */
    public boolean exists() {
        return this.exists;
    }

    /**
     * @return String representation of this label
     */
    @Override
    public String toString() {
        if (this.exists) {
            return this.ref + " != null";
        } else {
            return this.ref + " == null";
        }
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Existence Check");
        res.put("Checked Ref", this.ref.toString());
        res.put("Is null", this.exists);
        return res;
    }
}
