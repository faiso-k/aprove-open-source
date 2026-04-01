package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class holds information about read and write accesses to
 * static fields.
 *
 * @author Marc Brockschmidt
 */
public class StaticFieldAccessInformation implements AccessInformation {
    /** Yeah right. */
    private static final long serialVersionUID = 1L;

    /**
     *  Read or write access?
     */
    private final FieldAccessRW accessType;

    /**
     * Classname determining the the class to look at (think: class hierarchy)
     */
    private final ClassName className;

    /**
     * Name of the field to write to
     */
    private final String fieldName;

    /**
     * Accessed reference.
     */
    private final AbstractVariableReference accessedRef;

    /**
     * @param type Type of the access (i.e., read or write)
     * @param classN Classname determining the enclosing class of the accessed
     *  field.
     * @param fieldN Name of the accessed field.
     * @param ref Reference of the variable which is read from or written to
     *  the field.
     */
    public StaticFieldAccessInformation(final FieldAccessRW type,
            final ClassName classN, final String fieldN,
            final AbstractVariableReference ref) {
        this.accessType = type;
        this.className = classN;
        this.fieldName = fieldN;
        this.accessedRef = ref;
    }

    /**
     * @return the accessType
     */
    @Override
    public FieldAccessRW getAccessType() {
        return this.accessType;
    }

    /**
     * @return the accessedRef
     */
    @Override
    public AbstractVariableReference getAccessedRef() {
        return this.accessedRef;
    }
    /**
     * @return Classname determining the the class to look at (think: class
     *  hierarchy)
     */
    public ClassName getClassName() {
        return this.className;
    }

    /**
     * @return Name of the field to write to
     */
    public String getFieldName() {
        return this.fieldName;
    }

    /**
     * No need for a string representation.
     * @return the empty string.
     */
    @Override
    public String toString() {
        return "";
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Static Field Access");
        res.put("Access Type", this.getAccessType().toString());
        res.put("Field name", this.getClassName().toString() + "." + this.getFieldName());
        res.put("Result ref", this.getAccessedRef().toString());
        return res;
    }
}
