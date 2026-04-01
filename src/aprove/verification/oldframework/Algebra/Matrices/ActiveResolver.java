package aprove.verification.oldframework.Algebra.Matrices;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * This resolves the active conditions using the given Coefficients and goalState.
 * @author Patrick Kabasci
 * @version $Id$
 */
public class ActiveResolver {

    private Map<QActiveCondition, SimplePolynomial> activeConds = new LinkedHashMap<QActiveCondition, SimplePolynomial>();
    private Map<String, BigInteger> goalState;
    private boolean active = false;

    public boolean getActive() {
        return this.active;
    }

    public void setIsActive() {
        this.active = true;
    }

    public void specialize(Map<String, BigInteger> goalState) {
        this.goalState = goalState;
    }


    public void put(QActiveCondition which, SimplePolynomial what) {
        this.activeConds.put(which, what);
    }

    /**
     * Do NOT use this method to compute usable rules, since this does not guarantee
     * that the resulting set of usable rules is closed under right-hand sides.
     *
     * In the past, this resulted in non-certifiable proofs. See {@link AbstractMATRO#checkQActiveCondition}.
     */
    public boolean get(QActiveCondition which) {

        if (this.goalState == null) {
            throw new RuntimeException("Cannot query active status of a nonspecialized interpretation.");
        }
        if (this.active) {
            return !(this.activeConds.get(which).specialize(this.goalState).equals(SimplePolynomial.ZERO));
        } else {
            return true;
        }
    }


}

