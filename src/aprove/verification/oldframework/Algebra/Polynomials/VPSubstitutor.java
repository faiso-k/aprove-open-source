package aprove.verification.oldframework.Algebra.Polynomials;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Performs substitutions on VarPolynomials.
 * Memorizes which substitutions have already been performed.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class VPSubstitutor {

    // cache
    private LRUCache<Pair<VarPolynomial, Map<String, VarPolynomial>>, VarPolynomial> applied;

    private static final int cacheSizeLimit = 100; // an arbitrary choice

    public VPSubstitutor() {
        this.applied = new LRUCache<Pair<VarPolynomial, Map<String, VarPolynomial>>, VarPolynomial>(VPSubstitutor.cacheSizeLimit);
    }

    /**
     * Apply s to all of polys.
     *
     * @param polys
     * @param s
     * @return map s polys
     */
    public Set<VarPolynomial> substitute(Set<VarPolynomial> polys,
            Map<String, VarPolynomial> s) {
        Set<VarPolynomial> result = new LinkedHashSet<VarPolynomial>(polys.size());
        for (VarPolynomial vp : polys) {
            VarPolynomial newVP = this.substitute(vp, s);
            result.add(newVP);
        }
        return result;
    }

    /**
     * Apply s to vp, using the result cache in the process.
     *
     * @param vp
     * @param s
     * @return s(vp)<br><br>(i.e., s applied to vp)
     */
    public VarPolynomial substitute(VarPolynomial vp,
            Map<String, VarPolynomial> s) {
        Pair<VarPolynomial, Map<String, VarPolynomial>> input;
        input = new Pair<VarPolynomial, Map<String, VarPolynomial>>(vp, s);
        VarPolynomial result = this.applied.get(input);
        if (result == null) {
            result = vp.substituteVariables(s);
            this.applied.put(input, result);
        }
        return result;
    }

    @Override
    public String toString() {
        return this.applied.toString();
    }
}
