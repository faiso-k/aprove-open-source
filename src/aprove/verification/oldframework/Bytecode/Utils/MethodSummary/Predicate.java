package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import org.json.JSONObject;

public class Predicate {

    public final PredicateType type;
    public final String var0, var1;

    public Predicate(PredicateType type, String var0, String var1) {
        this.type = type;
        this.var0 = var0;
        this.var1 = var1;
    }

    public JSONObject toJSON() {
        JSONObject res = new JSONObject()
                .put("type", type.toString());
        if (var0 != null) {
            res.put("var0", var0.toString());
        }
        if (var1 != null) {
            res.put("var1", var1.toString());
        }
        return res;
    }
}
