package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This edge annotation denotes, that a reference has been checked against
 * a specific type.
 *
 * @author christian
 *
 */
public class InstanceCast implements ObjectInformation {
    /**
     * Reference, whose type has been checked
     */
    private final AbstractVariableReference ref;

    /**
     * @param ref Checked reference
     */
    public InstanceCast(final AbstractVariableReference ref) {
        this.ref = ref;
    }

    /**
     * @return Checked reference
     */
    @Override
    public AbstractVariableReference getRef() {
        return this.ref;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "Instance Cast " + this.ref;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Instance Cast");
        res.put("Checked ref", this.getRef().toString());
        return res;
    }
}
