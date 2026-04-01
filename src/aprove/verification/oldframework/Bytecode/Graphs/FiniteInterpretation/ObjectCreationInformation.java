package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class documents a reference as having been created.
 *
 * @author christian
 *
 */
public class ObjectCreationInformation implements ObjectInformation {
    /**
     * Reference documented as created
     */
    private final AbstractVariableReference ref;

    /**
     * Class of the newly created object
     */
    private final ClassName createdClass;

    /**
     * @param r created reference
     * @param createdC class of the created object
     */
    public ObjectCreationInformation(final AbstractVariableReference r, final ClassName createdC) {
        super();
        this.ref = r;
        this.createdClass = createdC;
    }

    /**
     * @return The created reference
     */
    @Override
    public AbstractVariableReference getRef() {
        return this.ref;
    }

    /**
     * @return The class of the created object
     */
    public ClassName getCreatedClass() {
        return this.createdClass;
    }

    @Override
    public String toString() {
        return "";
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Instance Created");
        res.put("Created ref", this.getRef().toString());
        res.put("Classname", this.createdClass.toString());
        return res;
    }
}
