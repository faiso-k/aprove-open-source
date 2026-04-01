package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Function from [type1]...[typen] to int
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntFunction extends SMTLIBFunction<SMTLIBIntValue> {

    private final Map<List<String>, BigInteger> result;

    private SMTLIBIntFunction(final List<String> domains, final String name) {
        super(domains, name);
        this.result = new LinkedHashMap<List<String>, BigInteger>();
    }

    public static SMTLIBIntFunction create(final List<String> domains, final String name) {
        return new SMTLIBIntFunction(domains, name);
    }

    @Override
    public String getRange(final SMTTypeTranslator types) {
        return types.integers();
    }

    @Override
    public void setResult(final List<String> vals, final String result) {
        this.result.put(vals, BigInteger.valueOf(Long.parseLong(result)));
    }

    public String getResultAsString() {
        return this.result.toString();
    }

    public Map<List<String>, BigInteger> getResultAsMap() {
        return this.result;
    }

}
