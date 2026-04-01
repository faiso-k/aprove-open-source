package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.Nat;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A binarizer for natural numbers.
 * Most of this is C&P from the older IndefiniteBinarizer.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class NatBinarizer extends Binarizer<BigIntImmutable> {

    public NatBinarizer(CircuitFactory circuitFactory) {
        super(circuitFactory);
    }

    /**
     * Returns the corresponding representation of an indefinite coefficient
     * of a polynomial which consists of as many propositional variables as
     * bits are needed for range. For a given indefinite, the result will
     * always be the same (it will be cached once it has been computed), so the
     * range passed to bin should be constant for a given value of indef.
     * IMPORTANT: You have to take care yourself that the variable only results
     * in values <= range by using side constraints. The given range is only
     * used for saving some bits in the representation.
     * See aprove.verification.oldframework.Algebra.Polynomials.SatSearch.
     *          AbstractSPCToCircuitConverter.excludeUpperBits.
     *
     * TODO introduce facility for setting certain positions of the
     *      result to ZERO or ONE (e.g. by masking)
     *
     * @param indef the indefinite to be represented in propositional logic
     * @param range the range of the indefinite, at least 1
     * @return the representation of <code>indef</code> by <code>bits</code>
     *  propositional variables
     */
    @Override
    public PolyCircuit bin(String indef, BigIntImmutable range) {
        BigInteger max = range.getBigInt();
        if (Globals.useAssertions) {
            assert (max.signum() > 0) : "indef " + indef;
            assert (indef != null);
        }
        PolyCircuit result = this.indefsToVars.get(indef);
        if (result == null) {
            result = this.externalIndefsToFormulae.get(indef);
            if (result == null) {
                int bits = max.bitLength();
                List<Formula<None>> resultX;
                resultX = new ArrayList<Formula<None>>(bits);
                for (int i = 0; i < bits; ++i) {
                    resultX.add(this.formulaFactory.buildVariable());
                }

                result = new PolyCircuit(resultX, max);
                this.indefsToVars.put(indef, result);
            }
        }
        // build range constraint only if necessary, i.e. if the binarized
        // representation would allow for values greater than the specified
        // maximum value.
        if (max.compareTo(BigInteger.valueOf(2).pow(max.bitLength())) < 0) {
            this.rangeConstraints.add(this.circuitFactory.buildGTCircuit(
                    this.bin(BigIntImmutable.create(range.getBigInt().add(BigInteger.ONE))),
                    result.getFormulae()));
        }
        return result;
    }

    /**
     * Create a circuit that represents the given constant.
     * @param n to be represented as a binary in propositional logic
     * @return the circuit for n.
     */
    @Override
    public PolyCircuit toCircuit(final BigIntImmutable n) {
        if (n == null) {
            return this.one();
        } else {
            List<Formula<None>> formulaList = this.bin(n);
            return new PolyCircuit(formulaList, n.getBigInt());
        }
    }

    /**
     * @param n to be represented as a binary in propositional logic
     * @return the binary representation of <code>n</code> in
     *  propositional logic
     */
    @Override
    public List<Formula<None>> bin(final BigIntImmutable n) {
        BigInteger m = n.getBigInt();
        if (Globals.useAssertions) {
            assert (m.signum() >= 0);
        }

        if (m.signum() == 0) {
            List<Formula<None>> result = new ArrayList<Formula<None>>(1);
            result.add(this.ZERO);
            return result;
        }

        // length = ceil(log_2(n+1));
        int length = m.bitLength(); //32 - Integer.numberOfLeadingZeros(n);
        List<Formula<None>> result = new ArrayList<Formula<None>>(length);

        for (int i = 0; i < length; ++i) {
            boolean ithBitIsSet = m.testBit(i);
            result.add(ithBitIsSet ? this.ONE : this.ZERO);
        }

        if (Globals.useAssertions) {
            assert (result.get(length - 1) != this.ZERO);
        }

        return result;
    }

    /**
     * Computes the natural number that corresponds to vars given
     * interpretation. I.e.:
     *  sum over all indices i of atoms
     *    2^i*interpretation(vars.get(i))
     *  (true == 1, false == 0),
     *  constants are interpreted the natural way
     *
     * @param atoms the list of variables which are supposed to represent
     *  an indefinite coefficient, at most 31 ones
     * @return the corresponding natural number
     */
    @Override
    public BigIntImmutable toValue(List<? extends Formula<None>> formulae) {
        if (Globals.useAssertions) {
            assert (formulae.size() <= 31);
        }

        BigIntImmutable cachedValue = super.toValue(formulae);
        if (cachedValue != null) {
            return cachedValue;
        }

        int value = 0;
        int twoToTheN = 1;
        for (Formula<None> f : formulae) {
            if (f.isConstant()) {
                // constants don't care about interpretations
                int gateType = f.getGateType();
                if (gateType == CircuitGate.TRUE) {
                    value += twoToTheN;
                }
            } else if (this.interpretation.contains(f.getId())) {
                // variables or non-atomic formulae do in general, though
                value += twoToTheN;
            } else if (f.getId() == AbstractFormula.ID_UNSET) {
                // some formulae do not get to enter the actual CNF encoding,
                // so there is no Tseitin variable for them; get their truth
                // values in the classic style (if some actual variables of
                // theirs did not make it to the CNF either, it means that
                // their truth value does not matter overall, and we can
                // safely assume them to be 'false'
                if (f.interpret(this.interpretation)) {
                    value += twoToTheN;
                }
            }
            twoToTheN <<= 1; // twoToTheN *= 2;
        }

        BigIntImmutable result = BigIntImmutable.create(BigInteger.valueOf(value));
        this.coeffValues.put(formulae, result);
        return result;
    }

    @Override
    public PolyCircuit one() {
        return new PolyCircuit(
            this.bin(BigIntImmutable.create(BigInteger.ONE)),
                BigInteger.ONE);
    }

    @Override
    public PolyCircuit zero() {
        return new PolyCircuit(
            this.bin(BigIntImmutable.create(BigInteger.ZERO)),
                BigInteger.ONE);
    }
}
