package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

public class ConstantFloatCreationInformation implements FloatInformation {
    private final AbstractVariableReference var;
    private final AbstractFloat value;

    public ConstantFloatCreationInformation(
            final AbstractVariableReference ref, final AbstractFloat value) {
        this.value = value;
        this.var = ref;
    }

    public AbstractVariableReference getVar() {
        return this.var;
    }

    public AbstractFloat getValue() {
        return this.value;
    }

    /**
     * @return a readable string representation
     */
    @Override
    public String toString() {
        // This is boring as hell.
        return "";
        /*
        final StringBuilder sb = new StringBuilder("push: ");
        if (this.var != null) {
            sb.append(this.var.toString());
        }
        sb.append(" with value ");
        if (this.value != null) {
            sb.append(this.value.toString());
        }
        return sb.toString();
        */
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Float Constant");
        res.put("Float ref", this.getVar().toString());
        res.put("Float value", this.getValue().toString());
        return res;
    }
}
