package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import immutables.*;

/**
 * This represents the implication
 * <code>t1 >= 0 and t2 >= 0 ... tn >= 0 => p1 >= 0 and p2 >= 0 ... pm >= 0</code>.
 *
 * <p><code>t1 ... tn</code> are stored in <code>premises</code> and contain no variables
 * from <code>existentialVars</code>. <code>p1 ... pm</code> are stored in
 * <code>consequences</code> and may contain variables from <code>existentialVars</code>.
 */
public class RatPolImplication implements Immutable {
    public final ImmutableSet<String> existentialVars;
    public final ImmutableSet<RationalPolynomial> premises;
    public final ImmutableSet<RationalPolynomial> consequences;

    public RatPolImplication(
        ImmutableSet<String> existentialVars,
        ImmutableSet<RationalPolynomial> premises,
        ImmutableSet<RationalPolynomial> consequences)
    {
        this.existentialVars = existentialVars;
        this.premises = premises;
        this.consequences = consequences;
    }

    /**
     * Return {@code true} iff the (quantified) degree of all {@code consequences} is at most one.
     * @return
     */
    public boolean isLinear() {
        for (RationalPolynomial p : this.consequences) {
            if (!p.isLinearOnVars(this.existentialVars)) {
                return false;
            }
        }
        return true;
    }
}
