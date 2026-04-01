package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Function from [type1]...[typen] to bool
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolFunction extends SMTLIBFunction<SMTLIBBoolValue> {
    private final Map<List<String>, Boolean> result;

    private SMTLIBBoolFunction(final List<String> domains, final String name) {
        super(domains, name);
        this.result = new LinkedHashMap<List<String>, Boolean>();
    }

    public static SMTLIBBoolFunction create(final List<String> domains, final String name) {
        return new SMTLIBBoolFunction(domains, name);
    }

    @Override
    public String getRange(final SMTTypeTranslator types) {
        return types.bools();
    }

    public String getResultAsString() {
        return this.result.toString();
    }

    public Map<List<String>, Boolean> getResultAsMap() {
        return this.result;
    }

    @Override
    public void setResult(final List<String> vals, final String result) {
        this.result.put(vals, Boolean.valueOf(result));
    }
}
