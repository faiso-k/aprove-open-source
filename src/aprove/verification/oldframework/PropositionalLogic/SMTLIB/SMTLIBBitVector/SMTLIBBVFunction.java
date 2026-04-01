package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Function from [type1]...[typen] to int
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVFunction extends SMTLIBFunction<SMTLIBBVValue> {

    private final int len;
    private final Map<List<String>, Integer> result;

    private SMTLIBBVFunction(final List<String> domains, final String name, final int len) {
        super(domains, name);
        this.len = len;
        this.result = new LinkedHashMap<List<String>, Integer>();
    }

    public static SMTLIBBVFunction create(final List<String> domains, final String name, final int len) {
        return new SMTLIBBVFunction(domains, name, len);
    }

    @Override
    public void setResult(final List<String> vals, final String result) {
        String entry;
        if (result.startsWith("0b")) {
            entry = result.substring(2);
        } else {
            entry = result;
        }
        this.result.put(vals, Integer.parseInt(entry,2));
    }

    @Override
    public String getRange(final SMTTypeTranslator types) {
        return types.bitvectors(this.len);
    }

    public String getResultAsString() {
        return this.result.toString();
    }

    public Map<List<String>, Integer> getResultAsMap() {
        return this.result;
    }

}
