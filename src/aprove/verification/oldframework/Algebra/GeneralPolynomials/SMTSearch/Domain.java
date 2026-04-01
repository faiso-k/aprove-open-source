package aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch;

import java.math.*;
import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

public class Domain {

    private List<MbyN> domain;

    @ParamsViaArgumentObject
    public Domain(Arguments arguments) {
        this.domain = arguments.domain;
    }

    public static List<MbyN> createDomain(String string) {
        // a string domain should look like: [0, 1/4, 1/2, 0, 1, 2]
        List<MbyN> domain = new LinkedList<MbyN>();
        if (string.startsWith("[") && string.endsWith("]")) {
            string = string.substring(1, string.length() - 1);
            String[] numbers = string.split(",");
            for (String s : numbers) {
                MbyN dom = MbyN.create(s);

                domain.add(dom);
            }
        } else {

        }
        return domain;
    }

    public List<MbyN> getDomain() {
        return this.domain;
    }

    @Override
    public String toString() {
        return this.domain.toString();
    }

    public static enum MyPredefEnum {
        Q1("[0, 1]"),
        Q2("[0, 1/2, 1, 2]"),
        Q4("[0, 1/4, 1/2, 1, 2, 4]"),
        Q8("[0, 1/8, 1/4, 1/2, 1, 2, 4, 8]"),
 Q16("[0, 1/16, 1/8, 1/4, 1/2, 1, 2, 4, 8, 16]"), D4("[0, 1/4, 2/4, 3/4, 1, 5/4, 6/4, 7/4, 2, 9/4, 10/4, 11/4, 3, 13/4, 14/4, 15/4, 4]"),
        D2T8("[0, 1/2, 1/4, 1/6, 1/8]"),
        D2T16("[0, 1/2, 1/4, 1/6, 1/8, 1/10, 1/12, 1/14, 1/16]"),
        D4T16("[0, 1/4, 1/8, 1/12, 1/16]"),
        D4T32("[0, 1/4, 1/8, 1/12, 1/16, 1/20, 1/24, 1/28, 1/32]"),
        ;

        private final String stringDomain;

        private MyPredefEnum(String stringDomain) {
            this.stringDomain = stringDomain;
        }

        public List<MbyN> getDomain() {
            return Domain.createDomain(this.stringDomain);
        }

    }

    public static class Arguments {
        private List<MbyN> domain;

        public void setStringDomain(String domainString) {
            this.domain = Domain.createDomain(domainString);
        }

        public void setPredefDomain(MyPredefEnum domainEnum) {
            this.domain = domainEnum.getDomain();
        }

    }

    public MbyN getFirst() {
        return this.domain.get(0);
    }

    public MbyN getLast() {
        return this.domain.get(this.domain.size() - 1);
    }

    public static BigInteger getLCMofDenominator(Domain domain) {
        BigInteger lcm = BigInteger.ONE;
        for (MbyN coeff : domain.getDomain()) {
            BigInteger aTimesb = lcm.multiply(coeff.getDenominator());
            BigInteger gcd = lcm.gcd(coeff.getDenominator());
            lcm = aTimesb.divide(gcd);
        }
        return lcm;
    }

}
