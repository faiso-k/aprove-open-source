package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

public class ArrayLengthInfo implements VariableInformation {
    /**
     * array reference
     */
    private final AbstractVariableReference arrayReference;

    /**
     * reference of array length
     */
    private final AbstractVariableReference lengthReference;

    @Override
    public String toString() {
        return this.arrayReference + " has length " + this.lengthReference;
    }

    public ArrayLengthInfo(final AbstractVariableReference array, final AbstractVariableReference length) {
        this.arrayReference = array;
        this.lengthReference = length;
    }

    public AbstractVariableReference getArrayReference() {
        return this.arrayReference;
    }

    public AbstractVariableReference getLengthReference() {
        return this.lengthReference;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Array Length");
        res.put("Array ref", this.getArrayReference().toString());
        res.put("Length ref", this.getLengthReference().toString());
        return res;
    }
}
