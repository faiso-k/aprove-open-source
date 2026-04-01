package aprove.verification.oldframework.Algebra.Polynomials.PBSearch;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public interface PBChecker {

    /**
     * Note that the semantics of result of this method are slightly different
     * from those of SatChecker.check()!
     *
     * @param linSpcs - treated as a collection of linear PB constraints
     *  with indefinites x1, x2, ..., xn (if you provide something else,
     *  strange things may and probably will happen)
     * @param maximizeMe - if non-null, the underlying PB solver is asked
     *  to maximize maximizeMe while satisfying linSpcs (if supported)
     * @param maxVar - n (see above)
     * @param aborter
     * @return a model I of spcs where I[i] > 0 means that I(xi) = 1
     *  and I[i] < 0 means I(xi) = 0 (I[0] may be arbitrary) if the used
     *  PBSolver finds one; null otherwise
     * @throws AbortionException
     */
    public int[] check(Collection<SimplePolyConstraint> linSpcs, SimplePolynomial maximizeMe,
            int maxVar, final Abortion aborter) throws AbortionException;
}
