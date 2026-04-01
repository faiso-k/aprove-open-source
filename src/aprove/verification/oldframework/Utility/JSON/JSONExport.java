package aprove.verification.oldframework.Utility.JSON;

/**
 * Interface for objects offering a JSON export.
 * @author cryingshadow
 * @version $Id$
 */
public interface JSONExport {

    /**
     * @return This object as a JSON compatible object (null, Boolean, Number, JSONArray, JSONObject, or String).
     */
    public Object toJSON();

}
