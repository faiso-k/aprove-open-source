package aprove.verification.oldframework.Algebra.LimitPolynomials;

import aprove.verification.oldframework.Algebra.Polynomials.*;


/**
 * Encodes a constraint of LimitVarPolynomials.
 * It is represented as a single LimitVarPolynomial, thus to construct a ~ b use a-b ~ 0.
 * @author kabasci
 *
 */
public class LimitVarPolynomialConstraint {

    private LimitVarPolynomial capsule;
    private ConstraintType rel;

    /**
     * This encodes a new Constraint of a LimitVarPolynomial versus 0.
     * @param constraint The constraint to encode
     * @param relation One of >,>=,=
     */
    public LimitVarPolynomialConstraint(LimitVarPolynomial constraint, ConstraintType relation) {
        this.capsule=  constraint;
        this.rel = relation;
    }


    /**
     * @return the capsule
     */
    public LimitVarPolynomial getPolynomial() {
        return this.capsule;
    }



    /**
     * @return the rel
     */
    public ConstraintType getRel() {
        return this.rel;
    }



}
