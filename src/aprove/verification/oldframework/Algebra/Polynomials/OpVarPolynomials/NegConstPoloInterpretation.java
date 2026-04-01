package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Finding Polynomial Orders with negative constants in the interpretations
 * of the function symbols. As opposed to the old approximation-based
 * approach, here we represent max(.,0) as such.
 *
 * @author fuhs
 * @version $Id$
 */
public class NegConstPoloInterpretation extends NegCoeffPoloInterpretation {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.NegConstPoloInterpretation");

    /**
     * for abstract polynomial interpretations
     *
     * @param posRange
     * @param negRange
     */
    protected NegConstPoloInterpretation(BigInteger posRange, BigInteger negRange,
            NCInterHeuristic interHeuristic,
            SimplificationMode simplificationMode, boolean stripExponents) {
        super(posRange, negRange, interHeuristic,
                simplificationMode, stripExponents, false);
    }

    /**
     * for resulting concrete interpretations
     *
     * @param inter
     */
    protected NegConstPoloInterpretation(Map<FunctionSymbol, VarPolynomial> inter) {
        super(inter, false);
    }

    /**
     *
     * @param P
     * @param R
     * @param posRange
     * @param negRange
     * @param allStrict
     * @param interHeuristics
     * @param dioSatConv
     * @param engine
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public static NegCoeffPOLO solve(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            BigInteger posRange, BigInteger negRange, boolean allStrict,
            NCInterHeuristic interHeuristics,
            SimplificationMode simplificationMode, boolean stripExponents,
            DiophantineSATConverter dioSatConv, Engine engine,
            Abortion aborter) throws AbortionException {
        long millisTotal1, millisTotal2;
        millisTotal1 = System.currentTimeMillis();
        NegConstPoloInterpretation inter = new NegConstPoloInterpretation(posRange, negRange,
                interHeuristics, simplificationMode, stripExponents);

        NegCoeffPOLO result = inter.actuallySolve(P, R,
                allStrict, dioSatConv, engine, aborter);
        millisTotal2 = System.currentTimeMillis();
        if (NegConstPoloInterpretation.log.isLoggable(Level.FINE)) {
            NegConstPoloInterpretation.log.fine("The search for a POLO with negative constants took " +
                    (millisTotal2 - millisTotal1) + " ms in total.\n");
        }
        return result;
    }


    /**
     * When only the constants are negative, we may use the relation GE
     * for the usable rules.
     */
    @Override
    protected OpVPC encodeLeftRightR(OpVarPolynomial left, OpVarPolynomial right) {
        return new OpVPC(left, right, ConstraintType.GE);
    }

    @Override
    protected OrderRelation getUsableRulesRelation() {
        return OrderRelation.GE;
    }

    /**
     * Returns the (linear) interpretation for f.
     * Creates a new interpretation if necessary.
     * Each interpretation for a n-ary f is a polynomial in
     * the variables x_1 to x_n, where x_ is the common variable prefix.
     *
     * As opposed to the superclass, here we use non-negative factors
     * for coefficients and only allow negative constants.
     *
     * @param f
     * @return
     */
    @Override
    public VarPolynomial getInterpretation(FunctionSymbol f) {
        VarPolynomial vp = this.interpretation.get(f);
        if (vp == null) {
            int n = f.getArity();
            boolean heuristicAllowsNegConst = this.interHeuristic.useNegConst(f);

            // start with the constant part ...
            String coeff = this.getNextCoeff();
            SimplePolynomial sp = SimplePolynomial.create(coeff);

            if (n > 0 && heuristicAllowsNegConst) {
                sp = sp.plus(this.negRangePoly);
            }
            else { // negative addends only make sense for non-constants
                this.ranges.put(coeff, this.posRange);
            }
            vp = VarPolynomial.create(sp);

            // ... then carry on with the part of the interpretation of f
            // that contains variables
            for (int i = 0; i < n; ++i) {
                coeff = this.getNextCoeff();
                sp = SimplePolynomial.create(coeff);
                this.ranges.put(coeff, this.posRange);
                VarPolynomial addend = VarPolynomial.createVariable(NegCoeffPoloInterpretation.VAR_PREFIX+(i+1)).times(sp);
                vp = vp.plus(addend);
            }
            this.interpretation.put(f, vp);
        }
        return vp;
    }
}
