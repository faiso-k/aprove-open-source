package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 *
 * This class holds information about write access happening to instances
 *
 * @author christian
 *
 */
public class InstanceAccessInformation extends ReferenceAccessInformation implements ObjectInformation {
    /**
     * Classname determining the the class to look at (think: class hierarchy)
     */
    private final ClassName className;

    /**
     * Name of the field to write to
     */
    private final String fieldName;

    /**
     * The reference overwritten
     */
    private final AbstractVariableReference overwrittenRef;

    /**
     * @param type Type of the access (i.e., read or write)
     * @param ref Reference of the instance which is the target of the write
     * @param overwrittenR Reference which was in that field before
     * @param value Reference of the variable which is written to the field
     * @param classN Classname determining the the class to look at (think: class hierarchy)
     * @param fieldN Name of the field to write to
     */
    public InstanceAccessInformation(
        final FieldAccessRW type,
        final AbstractVariableReference ref,
        final AbstractVariableReference overwrittenR,
        final AbstractVariableReference value,
        final ClassName classN,
        final String fieldN)
    {
        super(type, ref, value);
        this.className = classN;
        this.fieldName = fieldN;
        this.overwrittenRef = overwrittenR;
    }

    /**
     * @return Reference of the instance which is the target of the write
     */
    @Override
    public AbstractVariableReference getRef() {
        return this.getReadOrWrittenRef();
    }

    /**
     * @return Reference of the instance which is was overwritten
     */
    public AbstractVariableReference getOverwrittenRef() {
        return this.overwrittenRef;
    }

    /**
     * @return Classname determining the the class to look at (think: class hierarchy)
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
     * @return identifier for the field written or read
     */
    public FieldIdentifier getFieldIdentifier() {
        return new FieldIdentifier(this.className, this.fieldName);
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
        res.put("Information Type", "Instance Access");
        res.put("Access Type", this.getAccessType().toString());
        res.put("Accessed ref", this.getAccessedRef().toString());
        res.put("Field name", this.getClassName().toString() + "." + this.getFieldName());
        res.put("Result ref", this.getReadOrWrittenRef().toString());
        return res;
    }
}
