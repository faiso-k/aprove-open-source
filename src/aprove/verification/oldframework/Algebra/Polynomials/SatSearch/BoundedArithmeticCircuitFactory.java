package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Like an ArithmeticCircuitFactory, but works with maximal output register
 * lengths both for products and for sums. The overflowing bits are stored
 * inside of this, and their negation must be ANDed to the corresponding
 * atomic constraint in the circuit for which the instance of this class
 * is used.
 *
 * Get them via getOverflows(). Reset them via resetOverflows().
 *
 * See also the paper on Matrix Interpretations for Term Rewriting (IJCAR 06).
 *
 * Note that the overflows really must be applied locally:
 *
 * Let a, b range over [0..3], allow at most 2 bits.
 * Then
 *
 *   (a >= 3 and b >= 3) or a + b >= 7
 *
 * is SATisfied if the overflows are applied locally (a = 3, b = 3).
 * If one were to enforce the overflows being ZERO as *global* side
 * constraint, one would implicitly add  3 >= a + b  as a side constraint.
 * This would be sound, but incomplete.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class BoundedArithmeticCircuitFactory extends ArithmeticCircuitFactory {


    private final int sumLimit; // max number of bits for sums
                                // (proper ones, i.e., outside times)
    private final int productLimit; // max number of bits for products

    // the corresponding maximum values
    private final BigInteger sumMax;
    private final BigInteger productMax;

    private List<Formula<None>> overflows;
    // global variable used for storing the overflow bits

    /**
     * @param circuitFactory  to be used internally
     * @param sumLimit  max number of bits the result of a sum may have
     * @param productLimit  max number of bits the result of a product may have
     */
    private BoundedArithmeticCircuitFactory(FormulaFactory<None> circuitFactory,
            int sumLimit, int productLimit, PoloSatConfigInfo config) {
        super(circuitFactory, config);
        this.sumLimit = sumLimit;
        this.productLimit = productLimit;
        BigInteger two = BigInteger.valueOf(2l);
        this.sumMax = two.pow(sumLimit).subtract(BigInteger.ONE);
        this.productMax = two.pow(productLimit).subtract(BigInteger.ONE);
        this.overflows = new ArrayList<Formula<None>>(2048);
    }

    /**
     * @param circuitFactory  to be used internally
     * @param sumLimit  max number of bits the result of a sum may have
     * @param productLimit  max number of bits the result of a product may have
     */
    public static BoundedArithmeticCircuitFactory create(FormulaFactory<None> circuitFactory,
            int sumLimit, int productLimit, PoloSatConfigInfo config) {
        return new BoundedArithmeticCircuitFactory(circuitFactory, sumLimit, productLimit, config);
    }


    @Override
    public PolyCircuit buildPlusCircuit(PolyCircuit xs, PolyCircuit ys) {
        PolyCircuit unboundedResult = super.buildPlusCircuit(xs, ys);
        List<Formula<None>> formulae = unboundedResult.getFormulae();
        int totalSize = formulae.size();
        if (totalSize > this.sumLimit) {
            List<Formula<None>> resultFmlae = new ArrayList<Formula<None>>(formulae.subList(0, this.sumLimit));
            PolyCircuit result = new PolyCircuit(resultFmlae, this.sumMax);

            // intentional side effect follows
            this.overflows.addAll(formulae.subList(this.sumLimit, totalSize));
            return result;
        }
        else {
            return unboundedResult;
        }
    }

    @Override
    public PolyCircuit buildTimesCircuit(PolyCircuit xs, PolyCircuit ys) {
        PolyCircuit unboundedResult = super.buildTimesCircuit(xs, ys);
        List<Formula<None>> formulae = unboundedResult.getFormulae();
        int totalSize = formulae.size();
        if (totalSize > this.productLimit) {
            List<Formula<None>> resultFmlae = new ArrayList<Formula<None>>(formulae.subList(0, this.productLimit));
            PolyCircuit result = new PolyCircuit(resultFmlae, this.productMax);

            // intentional side effect follows
            this.overflows.addAll(formulae.subList(this.productLimit, totalSize));
            return result;
        }
        else {
            return unboundedResult;
        }
    }

    public List<Formula<None>> getOverflows() {
        return this.overflows;
    }

    public void resetOverflows() {
        this.overflows = new ArrayList<Formula<None>>(2048);
    }
}
