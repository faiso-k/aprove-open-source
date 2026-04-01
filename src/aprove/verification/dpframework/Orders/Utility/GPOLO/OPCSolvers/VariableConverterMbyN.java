/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A VariableConverterMbyN is able to extract the value of some Diophantine
 * variable out of the integer array provided by the sat searcher (which
 * includes the values for propositional variables).
 * @author cotto
 */
public class VariableConverterMbyN {
    /**
     * The solution found by the sat searcher.
     */
    private Map<GPolyVar, BigInteger> solution;

    /**
     * For each parametric variable store the variables defining the numerator
     * and denominator.
     */
    private Map<GPolyVar, Pair<GPolyVar, GPolyVar>> info =
        new LinkedHashMap<GPolyVar, Pair<GPolyVar, GPolyVar>>();

    /**
     * The fixed denominator (may be null for variable denominators).
     */
    private BigInteger denominator;

    /**
     * @param denom The fixed denominator, may be null.
     */
    public VariableConverterMbyN(final BigInteger denom) {
        if (Globals.useAssertions) {
            assert (denom == null || denom.signum() > 0);
        }
        this.denominator = denom;
    }

    /**
     * Set the solution.
     * @param solutionParam A solution that was found by a sat searcher.
     */
    public void setSolution(final Map<GPolyVar, BigInteger> solutionParam) {
        this.solution = solutionParam;
    }

    /**
     * @param numerators The numerator for a given parametric variable.
     * @param denominators The denominator for a given parametric variable.
     */
    public void setNumeratorsAndDenominators(
            final Map<GPolyVar, GPolyVar> numerators,
            final Map<GPolyVar, GPolyVar> denominators) {
        for (Map.Entry<GPolyVar, GPolyVar> entry : numerators.entrySet()) {
            GPolyVar key = entry.getKey();
            Pair<GPolyVar, GPolyVar> pair =
                new Pair<GPolyVar, GPolyVar>(
                        entry.getValue(), denominators.get(key));
            this.info.put(key, pair);
        }
    }

    /**
     * @return a map giving the m/n value for each parametric variable.
     */
    public Map<GPolyVar, MbyN> getMap() {
        Map<GPolyVar, MbyN> result =
            new LinkedHashMap<GPolyVar, MbyN>(this.info.size());
        for (Map.Entry<GPolyVar, Pair<GPolyVar, GPolyVar>> entry
                : this.info.entrySet()) {
            Pair<GPolyVar, GPolyVar> pair = entry.getValue();
            BigInteger a = this.solution.get(pair.x);
            BigInteger b = this.solution.get(pair.y);
            if (a == null) {
                a = BigInteger.ZERO;
            }
            if (b == null || b.signum() == 0) {
                if (this.denominator != null) {
                    // this is wrong for boolean variables, but the output for
                    // these is not needed
                    b = this.denominator;
                } else {
                    // denominator is zero?!
                    assert (false);
                }
            }
            BigInteger gcd = a.gcd(b);
            a = a.divide(gcd);
            b = b.divide(gcd);
            MbyN res = MbyN.create(a, b);
            result.put(entry.getKey(), res);
        }
        return result;
    }
}
