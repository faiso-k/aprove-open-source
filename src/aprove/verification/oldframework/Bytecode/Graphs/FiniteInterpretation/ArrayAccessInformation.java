package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Convenience class to mark evaluation edges of array access operations.
 * @author Marc Brockschmidt
 */
public class ArrayAccessInformation extends ReferenceAccessInformation {
    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = 405054771178382986L;

    /**
     * Index of the accessed element.
     */
    private final AbstractVariableReference indexRef;

    /**
     * @param type Type of the access (i.e., read or write)
     * @param ref Reference of the instance which is the target of the write
     * @param value Reference of the variable which is written to the field
     * @param indexR Reference to the variable holding the accessed array index.
     */
    public ArrayAccessInformation(final FieldAccessRW type,
        final AbstractVariableReference ref,
        final AbstractVariableReference value,
        final AbstractVariableReference indexR) {
        super(type, ref, value);
        this.indexRef = indexR;
    }
    /**
     * @return the type of this array access.
     */
    public AbstractVariableReference getIndexRef() {
        return this.indexRef;
    }

    /**
     * @return the empty string.
     */
    @Override
    public String toString() {
        return "";
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Array Access");
        res.put("Access Type", this.getAccessType().toString());
        res.put("Accessed ref", this.getAccessedRef().toString());
        res.put("Index ref", this.getIndexRef().toString());
        res.put("Result ref", this.getReadOrWrittenRef().toString());
        return res;
    }
}
