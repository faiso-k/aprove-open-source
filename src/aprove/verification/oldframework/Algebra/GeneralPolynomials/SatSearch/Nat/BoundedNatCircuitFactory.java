package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.Nat;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Like NatCircuitFactory, but works with maximal output values
 * both for products and for sums. The overflowing bits are stored
 * inside of this, and their negation must be ANDed to the corresponding
 * atomic constraint in the circuit for which the instance of this class
 * is used.
 *
 * Get them via getOverflows(). Reset them via reset().
 *
 * See also the paper on Matrix Interpretations for Term Rewriting (IJCAR 06).
 *
 * Overflows are stored globally, so you should use this factory for just
 * a single Diophantine problem.
 *
 * Note that the overflows really must be applied locally:
 *
 * Let a, b range over [0..3], allow at most 2 bits.
 * Then
 *
 *   (a >= 3 and b >= 3) or a + b >= 7
 *
 * is SATisfied if the overflows are applied locally (a = 3, b = 3).
 * If one were to enforce the overflows being ZERO as global side
 * constraint, one would implicitly add  3 >= a + b  as a side constraint.
 * This would be sound, but incomplete.
 *
 * The class is a modified copy of BoundedArithmeticCircuitFactory.
 * Here we support also bounds that are not of the form 2^k - 1, though.
 *
 * @author Carsten Fuhs
 */
public class BoundedNatCircuitFactory extends NatCircuitFactory implements BoundedCircuitFactory {


    private final int sumBits; // max number of bits for sums
                               // (proper ones, i.e., outside times)
    private final int productBits; // max number of bits for products

    // the corresponding maximum values
    private final BigIntImmutable sumMaxBigIntImmutable;
    private final BigIntImmutable productMaxBigIntImmutable;

    private final BigInteger sumMax;
    private final BigInteger productMax;

    // do we use bounds for sums/products?
    private final boolean boundSums;
    private final boolean boundProducts;

    // do we need explicit >=-constraints for sums/products?
    private final boolean needGTForSums;
    private final boolean needGTForProducts;

    // cached values
    private List<Formula<None>> propSumMax;
    private List<Formula<None>> propProductMax;

    // needed if the allowed max values are not of the form 2^k - 1
    private Binarizer<BigIntImmutable> binarizer;

    private List<Formula<None>> overflows;
    // global variable used for storing the overflow bits

    /**
     * @param formulaFactory  to be used internally
     * @param maxSumValue  max value the result of a sum may have,
     *  <= 0 means unbounded
     * @param maxProductValue  max value the result of a product may have,
     *  <= 0 means unbounded
     */
    private BoundedNatCircuitFactory(FormulaFactory<None> formulaFactory,
            BigIntImmutable maxSumValue, BigIntImmutable maxProductValue) {
        super(formulaFactory);

        // init sum-related things
        this.sumMaxBigIntImmutable = maxSumValue;
        BigInteger sumMax = maxSumValue.getBigInt();
        this.sumMax = sumMax;
        this.sumBits = sumMax.bitLength();
        if (sumMax.signum() <= 0) {
            this.boundSums = false;
            this.needGTForSums = false;
        }
        else {
            this.boundSums = true;

            // positive numbers are of the shape 2^k - 1
            // iff all their bits are set to ONE
            this.needGTForSums = sumMax.bitCount() != this.sumBits;
        }

        // ditto for products
        this.productMaxBigIntImmutable = maxProductValue;
        BigInteger productMax = maxProductValue.getBigInt();
        this.productMax = productMax;
        this.productBits = productMax.bitLength();
        if (productMax.signum() <= 0) {
            this.boundProducts = false;
            this.needGTForProducts = false;
        }
        else {
            this.boundProducts = true;

            // positive numbers are of the shape 2^k - 1
            // iff all their bits are set to ONE
            this.needGTForProducts = productMax.bitCount() != this.productBits;
        }

        // for the rest!
        this.overflows = new ArrayList<Formula<None>>(2048);
        this.binarizer = null; // init later via setter
    }

    /**
     * @param formulaFactory  to be used internally
     * @param maxSumValue  max number of bits the result of a sum may have,
     *  <= 0 means unbounded
     * @param maxProductValue  max number of bits the result of a product may have,
     *  <= 0 means unbounded
     */
    public static BoundedNatCircuitFactory create(FormulaFactory<None> formulaFactory,
            BigIntImmutable maxSumValue, BigIntImmutable maxProductValue) {
        return new BoundedNatCircuitFactory(formulaFactory, maxSumValue, maxProductValue);
    }


    @Override
    public PolyCircuit buildPlusCircuit(PolyCircuit xs, PolyCircuit ys) {
        PolyCircuit unboundedResult = super.buildPlusCircuit(xs, ys);
        if (! this.boundSums) {
            return unboundedResult;
        }
        List<Formula<None>> formulae = unboundedResult.getFormulae();
        int totalSize = formulae.size();
        if (totalSize >= this.sumBits) {
            List<Formula<None>> resultFmlae;
            if (totalSize > this.sumBits) {
                resultFmlae = new ArrayList<Formula<None>>(formulae.subList(0, this.sumBits));

                // intentional side effect follows
                this.overflows.addAll(formulae.subList(this.sumBits, totalSize));
            }
            else { // totalSize == this.sumBits
                resultFmlae = formulae;
            }
            PolyCircuit result = new PolyCircuit(resultFmlae, this.sumMax);

            if (this.needGTForSums) {
                if (this.propSumMax == null) {
                    this.propSumMax = this.binarizer.bin(this.sumMaxBigIntImmutable);
                }
                Formula<None> sumExceedsMax =
                    this.buildGTCircuit(resultFmlae, this.propSumMax);
                this.overflows.add(sumExceedsMax);
            }
            return result;
        }
        else {
            return unboundedResult;
        }
    }

    /**
     * TODO
     * be more sophisticated by bounding those intermediate sums
     * explicitly during construction instead of just calling the
     * superclass method.
     */
    @Override
    public PolyCircuit buildTimesCircuit(PolyCircuit xs, PolyCircuit ys) {
        PolyCircuit unboundedResult = super.buildTimesCircuit(xs, ys);
        if (! this.boundProducts) {
            return unboundedResult;
        }
        List<Formula<None>> formulae = unboundedResult.getFormulae();
        int totalSize = formulae.size();
        if (totalSize >= this.productBits) {
            List<Formula<None>> resultFmlae;
            if (totalSize > this.productBits) {
                resultFmlae = new ArrayList<Formula<None>>(formulae.subList(0, this.productBits));

                // intentional side effect follows
                this.overflows.addAll(formulae.subList(this.productBits, totalSize));
            }
            else { // totalSize == this.sumBits
                resultFmlae = formulae;
            }
            PolyCircuit result = new PolyCircuit(resultFmlae, this.productMax);

            if (this.needGTForProducts) {
                if (this.propProductMax == null) {
                    this.propProductMax = this.binarizer.bin(this.productMaxBigIntImmutable);
                }
                Formula<None> productExceedsMax =
                    this.buildGTCircuit(resultFmlae, this.propProductMax);
                this.overflows.add(productExceedsMax);
            }
            return result;
        }
        else {
            return unboundedResult;
        }
    }

    public void setBinarizer(Binarizer<BigIntImmutable> b) {
        this.binarizer = b;
    }

    @Override
    public Overflows getOverflows() {
        return new Overflows(this.overflows);
    }

    @Override
    public void reset() {
        this.overflows = new ArrayList<Formula<None>>(2048);
    }

    /**
     * As indicated by the name, here we do use bounded arithmetic.
     */
    @Override
    public boolean usesBoundedArithmetic() {
        return true;
    }
}
