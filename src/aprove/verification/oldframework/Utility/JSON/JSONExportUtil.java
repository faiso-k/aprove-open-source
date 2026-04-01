package aprove.verification.oldframework.Utility.JSON;

import java.lang.reflect.*;
import java.util.*;

import org.json.*;

import immutables.*;

/**
 * Utility for JSON export.
 * @author cryingshadow
 * @version $Id$
 */
public class JSONExportUtil {

    /**
     * This method applies the best possible transformation of objects to JSON compatible objects (null, Number,
     * Boolean, JSONArray, JSONObject, String) also the the objects reachable from the specified object (i.e., if the
     * object is a collection, also the elements of the collection are transformed).
     * @param o Some object.
     * @return A JSONObject, JSONArray, String (according to the JSON format), Number, or Boolean representation of the
     *         specified object.
     */
    public static Object toJSON(Object o) {
        if (o == null) {
            return JSONObject.NULL;
        }
        if (o instanceof JSONExport) {
            return ((JSONExport)o).toJSON();
        }
        if (o instanceof Number || o instanceof Boolean) {
            return o;
        }
        if (o.getClass().isArray()) {
            int length = Array.getLength(o);
            Object[] array = new Object[length];
            for (int i = 0; i < length; i++) {
                array[i] = JSONExportUtil.toJSON(Array.get(o, i));
            }
            return new JSONArray(array);
        }
        if (o instanceof ImmutablePair) {
            ImmutablePair<?, ?> pair = (ImmutablePair<?, ?>)o;
            return new JSONArray(new Object[]{JSONExportUtil.toJSON(pair.x), JSONExportUtil.toJSON(pair.y)});
        }
        if (o instanceof ImmutableTriple) {
            ImmutableTriple<?, ?, ?> triple = (ImmutableTriple<?, ?, ?>)o;
            return
                new JSONArray(
                    new Object[]{
                        JSONExportUtil.toJSON(triple.x),
                        JSONExportUtil.toJSON(triple.y),
                        JSONExportUtil.toJSON(triple.z)
                    }
                );
        }
        if (o instanceof Map) {
            Map<?, ?> map = (Map<?, ?>)o;
            JSONObject res = new JSONObject();
            for (Map.Entry<?, ?> entry : map.entrySet()) {
                Object key = entry.getKey();
                if (key instanceof JSONExport) {
                    res.put(((JSONExport)key).toJSON().toString(), JSONExportUtil.toJSON(entry.getValue()));
                } else {
                    res.put(key.toString(), JSONExportUtil.toJSON(entry.getValue()));
                }
            }
            return res;
        }
        if (o instanceof Collection) {
            JSONArray res = new JSONArray();
            for (Object e : (Collection<?>)o) {
                res.put(JSONExportUtil.toJSON(e));
            }
            return res;
        }
        return o.toString();
    }

    /**
     * @param o Some object.
     * @return A JSON String for this object.
     */
    public static String toJSONString(Object o) {
        final int indentFactor = 4;
        Object transformed = JSONExportUtil.toJSON(o);
        if (transformed instanceof String) {
            return JSONObject.quote((String)transformed);
        }
        if (transformed instanceof JSONObject) {
            return ((JSONObject)transformed).toString(indentFactor);
        }
        if (transformed instanceof JSONArray) {
            return ((JSONArray)transformed).toString(indentFactor);
        }
        return transformed.toString();
    }

}
