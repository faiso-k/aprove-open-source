package aprove.verification.oldframework.Algebra.LimitPolynomials;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * LPOLInterpretor - Interprets Rules into LimitPolynomials
 * Generally, a Rule is interpreted into a LimitPolynomial for the ground part,
 * and a List of LimitPolynomials, one per Variable.
 *
 * For satisfying a rule, the Variable part must be >= for >= or >, and = for =,
 * and the ground part must be in the desired relation.
 * This is incomplete.
 * (Future work: Implement min ground constants, then a more complete transformation is possible)
 *
 * @author kabasci
 *
 */
public class LPOLInterpretor {

    /**
     * Store the representation of the function symbols etc.
     */
    LPOLSymbolRepresentations repres;

    /**
     * Create a new LPOLInterpretor using a new signature.
     * @param signature The P cup R signature of the Problem.
     */
    public LPOLInterpretor(final List<FunctionSymbol> signature, final int expRange) {
        this.repres = new LPOLSymbolRepresentations(signature, expRange);
    }

    /**
     * Create a new LPOLInterpretor given an existing representation.
     * @param repres
     */
    public LPOLInterpretor(final LPOLSymbolRepresentations repres) {
        this.repres = repres;
    }

    /**
     * Returns the Representations for specializing.
     * @return
     */
    public LPOLSymbolRepresentations getRepresentations() {
        return this.repres;
    }

    /**
     * Interpret a rule into a LimitPolynomial, such that l >/>=/=_LPOLO r <= result >/>=/= 0
     * @param r The rule to interpret
     * @return
     */

    public LimitVarPolynomialConstraint interpretRule(final Constraint<TRSTerm> r) {

        return new LimitVarPolynomialConstraint(
            this.interpretTerm(r.getLeft()).minus(this.interpretTerm(r.getRight())),
            this.toConstraintType(r.getType()));

    }

    /**
     * Interpret a rule into a LimitPolynomial, such that l >/>=/=_LPOLO r <= result >/>=/= 0
     * @param r The rule to interpret
     * @return
     */

    public LimitVarPolynomialConstraint interpretRule(final Rule r, final ConstraintType c) {

        return new LimitVarPolynomialConstraint(
            this.interpretTerm(r.getLeft()).minus(this.interpretTerm(r.getRight())),
            c);

    }

    /**
     * Interprets a single term into a LimitVarPolynomial.
     * @param t
     * @return
     */
    public LimitVarPolynomial interpretTerm(final TRSTerm t) {

        if (t instanceof TRSVariable) {
            return new LimitVarPolynomial(((TRSVariable) t));
        } else if (t instanceof TRSFunctionApplication) {
            // t = f(x_1,...,x_n)
            final List<LimitVarPolynomial> args = new ArrayList<LimitVarPolynomial>();
            // Note the -1, as in the symbol representations coefficient 0 is the constant coefficient, yet in FunctionApplication they are ordered zero-based.
            for (int i = 1; i <= ((TRSFunctionApplication) t).getRootSymbol().getArity(); i++) {
                LimitVarPolynomial arg = this.interpretTerm(((TRSFunctionApplication) t).getArgument(i - 1));
                arg = arg.multiplyBy(this.repres.getCoefficientPoly(((TRSFunctionApplication) t).getRootSymbol(), i));
                args.add(arg);
            }
            args.add(new LimitVarPolynomial(
                this.repres.getCoefficientPoly(((TRSFunctionApplication) t).getRootSymbol(), 0)));
            return LimitVarPolynomial.plus(args);
        } else {
            // This shall never happen.
            throw new IllegalStateException("Term is neither a variable nor a function application: " + t);
        }

    }

    private ConstraintType toConstraintType(final OrderRelation r) {

        if (r == OrderRelation.EQ || r == OrderRelation.GENGR) {
            return ConstraintType.EQ;
        } else if (r == OrderRelation.GE) {
            return ConstraintType.GE;
        } else if (r == OrderRelation.GR) {
            return ConstraintType.GT;
        } else {
            // default
            return ConstraintType.GE;
        }

    }

}
