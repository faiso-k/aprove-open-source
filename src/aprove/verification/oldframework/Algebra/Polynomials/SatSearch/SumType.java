package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

/**
 * There are many ways of computing n-ary sums since plus is associative
 * and commutative. Some of them can be chosen here.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public enum SumType {
    BALANCED_SORTED, // balanced sorted (wrt to leaf list length) tree
    BALANCED_UNSORTED, // balanced tree w/o any particular sorting
    COMB, // a comb
    MINIMAL, // neither necessarily a comb nor necessarily a balanced
            // tree, but the root tuple will have "minimal" length
            // (assuming that a sum has length one greater than
            // the maximum of the argument lengths)
    DUAL_COMB // a comb, but with mixed-dual-adders. Only works for unary shifts.
}
