package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Function from [type1]...[typen] to a rational number.
 *
 * @author CKuknat
 */
public class SMTLIBRatFunction extends SMTLIBFunction<SMTLIBRatValue> {

    private final Map<List<String>, MbyN> result;

    private SMTLIBRatFunction(final List<String> domains, final String name) {
        super(domains, name);
        this.result = new LinkedHashMap<List<String>, MbyN>();
    }

    public static SMTLIBRatFunction create(final List<String> domains, final String name) {
        return new SMTLIBRatFunction(domains, name);
    }

    @Override
    public String getRange(final SMTTypeTranslator types) {
        return types.rationals();
    }

    @Override
    public void setResult(final List<String> vals, final String result) {
        final BigInteger numerator = BigInteger.valueOf(Long.parseLong(result.substring(0, 1)));
        final BigInteger denominator = BigInteger.valueOf(Long.parseLong(result.substring(2)));
        this.result.put(vals, MbyN.create(numerator, denominator));
    }

    public String getResultAsString() {
        return this.result.toString();
    }

    public Map<List<String>, MbyN> getResultAsMap() {
        return this.result;
    }

}
