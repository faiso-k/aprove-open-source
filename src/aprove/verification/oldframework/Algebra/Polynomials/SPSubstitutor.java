package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Applies substitutions to SimplePolynomials. Since SimplePolynomials are
 * immutable, sharing effects can be achieved by caching in this class.
 *
 * @author fuhs
 */
public class SPSubstitutor {

    // cache
    private LRUCache<Pair<SimplePolynomial, Integer>, SimplePolynomial> powers;

    private static final int cacheSizeLimit = 100; // an arbitrary choice

    public SPSubstitutor() {
        this.powers = new LRUCache<Pair<SimplePolynomial, Integer>, SimplePolynomial>(SPSubstitutor.cacheSizeLimit);
    }

    /**
     * Apply s to all of polys.
     *
     * @param polys
     * @param s
     * @return map s polys
     */
    public Set<SimplePolynomial> substitute(Set<SimplePolynomial> polys,
            Map<String, SimplePolynomial> s) {
        Set<SimplePolynomial> result = new LinkedHashSet<SimplePolynomial>(polys.size());
        for (SimplePolynomial sp : polys) {
            SimplePolynomial newSP = this.substitute(sp, s);
            result.add(newSP);
        }
        return result;
    }

    /**
     * @param sp
     * @param s
     * @return s(sp)<br><br>(s applied to sp)
     */
    public SimplePolynomial substitute(SimplePolynomial sp,
            Map<String, SimplePolynomial> s) {
        ImmutableMap<IndefinitePart, BigInteger> simpleMonomials;
        simpleMonomials = sp.getSimpleMonomials();

        List<SimplePolynomial> addends = new ArrayList<SimplePolynomial>();
        for (Entry<IndefinitePart, BigInteger> monomial : simpleMonomials.entrySet()) {
            ImmutableMap<String, Integer> exponents = monomial.getKey().getExponents();
            Map<String, Integer> newExps = new LinkedHashMap<String, Integer>();
            List<SimplePolynomial> factors = new ArrayList<SimplePolynomial>();
            for (Entry<String, Integer> exp : exponents.entrySet()) {
                String indef = exp.getKey();
                SimplePolynomial substitute = s.get(indef);
                if (indef == null) {
                    newExps.put(indef, exp.getValue());
                }
                else {
                    int power = exp.getValue();
                    if (power == 1) {
                        factors.add(substitute);
                    }
                    else {
                        SimplePolynomial substituteToPower = this.getPower(substitute, exp.getValue());
                        factors.add(substituteToPower);
                    }
                }
            }
            //   multiply remaining IP with corresponding substitutes
            IndefinitePart newExpsIP = IndefinitePart.create(newExps);
            SimplePolynomial substituteOfIP = SimplePolynomial.create(Collections.singletonMap(newExpsIP, monomial.getValue()));
            for (SimplePolynomial factor : factors) {
                substituteOfIP = substituteOfIP.times(factor);
            }
            addends.add(substituteOfIP);
        }

        SimplePolynomial result = SimplePolynomial.ZERO;
        for (SimplePolynomial addend : addends) {
            result = result.plus(addend);
        }
        return result;
    }

    /**
     * @param sp
     * @param n
     * @return sp^n (possibly from cache)
     */
    private SimplePolynomial getPower(SimplePolynomial sp, Integer n) {
        Pair<SimplePolynomial, Integer> pair = new Pair<SimplePolynomial, Integer>(sp, n);
        SimplePolynomial result = this.powers.get(pair);
        if (result == null) {
            result = sp.power(n);
            this.powers.put(pair, result);
        }
        return result;
    }
}
