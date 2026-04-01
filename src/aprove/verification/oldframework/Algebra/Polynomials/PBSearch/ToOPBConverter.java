package aprove.verification.oldframework.Algebra.Polynomials.PBSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class ToOPBConverter {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.PBSearch.ToOPBConverter");

    /**
     * @param spcsParam -- must contain linear polynomials with variables
     *  named x1, ..., xn
     * @param maximizeMe -- ditto (where not all of x1, ..., xn are required)
     * @param maxVar -- n
     * @param timesAsAsterisk -- true: write "*" for times (as in PB'05);
     *  false: just write " " instead (as of PB'07)
     * @param aborter
     * @return a String representation of spcs with maxVar as highest variable
     *  index if not trivially unsatisfiable (i.e., an unsatisfiable constraint
     *  without variables exists); null if trivially unsatisfiable
     * @throws AbortionException
     */
    public static String toOPB(Collection<SimplePolyConstraint> spcsParam, SimplePolynomial maximizeMe,
            int maxVar, boolean timesAsAsterisk, Abortion aborter) throws AbortionException {

        Collection<SimplePolyConstraint> spcs = ToOPBConverter.cleanse(spcsParam);
        if (spcs == null) {
            return null;
        }
        int numberOfVars = maxVar;
        int numberOfConstraints = spcs.size();
        ToOPBConverter.log.log(Level.FINE, "Cleansed {0} valid PB constraints",
                numberOfConstraints - spcsParam.size());

        StringBuilder pbSB = new StringBuilder(numberOfConstraints * 4);
        // conform to PB07 evaluation format for linear constraints

        // (1) preamble
        pbSB.append("* #variable= ");
        pbSB.append(numberOfVars);
        pbSB.append(" #constraint= ");
        pbSB.append(numberOfConstraints);
        pbSB.append("\n");

        // (2) optimization stuff (optional)
        if (maximizeMe != null) {
            SimplePolynomial minimizeMe = maximizeMe.negate();
            pbSB.append("min:");

            Map<IndefinitePart, BigInteger> simpleMonomials = minimizeMe.getSimpleMonomials();
            for (Entry<IndefinitePart, BigInteger> monomial : simpleMonomials.entrySet()) {
                IndefinitePart iPart = monomial.getKey();

                // ignore the constant, it does not matter
                boolean first = true;
                if (! iPart.isEmpty()) {
                    if (Globals.useAssertions) { // linearity!
                        assert iPart.size() == 1;
                    }
                    String pbVar = iPart.getExponents().keySet().iterator().next();
                    BigInteger factor = monomial.getValue();
                    pbSB.append(" ");
                    if (factor.signum() > 0 && !first) {
                        pbSB.append("+");
                    }
                    pbSB.append(factor);
                    pbSB.append((timesAsAsterisk) ? "*" : " ");
                    pbSB.append(pbVar);
                }
                first = false;
            }
            pbSB.append(" ;\n");
        }

        // (3) the actual constraints to be satisfied
        for (SimplePolyConstraint spc : spcs) {
            Map<IndefinitePart, BigInteger> simpleMonomials;
            simpleMonomials = spc.getPolynomial().getSimpleMonomials();
            boolean first = true;
            BigInteger theConstant = BigInteger.ZERO;
            for (Entry<IndefinitePart, BigInteger> monomial : simpleMonomials.entrySet()) {
                IndefinitePart iPart = monomial.getKey();
                if (iPart.isEmpty()) {
                    theConstant = monomial.getValue();
                }
                else {
                    if (Globals.useAssertions) { // linearity!
                        assert iPart.size() == 1;
                    }
                    String pbVar = iPart.getExponents().keySet().iterator().next();
                    BigInteger factor = monomial.getValue();
                    if (factor.signum() > 0 && !first) {
                        pbSB.append("+");
                    }
                    pbSB.append(factor);
                    pbSB.append((timesAsAsterisk) ? "*" : " ");
                    pbSB.append(pbVar);
                    pbSB.append(" ");
                }
                first = false;
            }
            switch (spc.getType()) {
            case GE :
                pbSB.append(">= ");
                break;
            case EQ :
                pbSB.append("= ");
                break;
            default :
                throw new RuntimeException(spc.getType() + " should not occur inside an SPC!");
            }
            // p + const >= / = 0 becomes p >= / = - const
            pbSB.append( theConstant.negate() );
            pbSB.append(" ;\n");
            aborter.checkAbortion();
        }
        String result = pbSB.toString();
        return result;
    }

    /**
     * @param spcs -- must contain linear polynomials with variables
     *  named x1, ..., xn, some elements may be valid of unsatisfiable
     * @return collection of equivalent spcs without valid or unsatisfiable
     *  elements; null if one of the elements of spcs is unsatisfiable
     */
    private static Collection<SimplePolyConstraint> cleanse(
            Collection<SimplePolyConstraint> spcs) {
        List<SimplePolyConstraint> res = new ArrayList<SimplePolyConstraint>(spcs.size());
        for (SimplePolyConstraint spc : spcs) {
            if (! spc.isSatisfiable()) {
                ToOPBConverter.log.log(Level.FINEST,
                        "PB Constraint {0} is trivially unsatisfiable!",
                        spc);
                return null;
            }
            if (! spc.isValid()) {
                res.add(spc);
            }
        }
        return res;
    }
}
