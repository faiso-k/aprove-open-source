package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A binarizer for (positive) exotic integers.
 *
 * Exotic numbers are represented by means of a flag bit, which is 1
 * iff the number is (negative) infinity, and the binarized numerical
 * value (which is, of course, only considered if the flag is zero).
 *
 * Since both arctic and tropical integers are treated completely
 * analogously, this code is able to handle both types.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ExoticIntBinarizer<T extends ExoticInt<T>> extends Binarizer<T> {

    /**
     * A factory for creating exotic integers. Used so we don't have to know
     * which actual type of exotic numbers we are working with.
     */
    protected final ExoticIntFactory<T> intFactory;

    /**
     * If this is > 0, all created circuits actually represent "a + shift",
     * and shift is subtracted from the values yielded by the SAT solver to
     * balance this out. Needed for "below zero" interpretations so we don't
     * have to binarize negative numbers.
     */
    protected int shift = 0;

    public ExoticIntBinarizer(
            final ExoticIntFactory<T> intFactory,
            final CircuitFactory circuitFactory) {
        super(circuitFactory);
        this.intFactory = intFactory;
    }

    @Override
    public PolyCircuit bin(final String indef, final T range) {

        BigInteger max;
        Formula<None> infFlag;

        if (Globals.useAssertions) {
            assert (indef != null);
        }

        if (range.equals(this.intFactory.zero()) || range.equals(this.intFactory.one())) {
            max = BigInteger.ONE;
        } else {
            max = range.getValue();
        }
        max = max.add(BigInteger.valueOf(this.shift));

        PolyCircuit result = this.indefsToVars.get(indef);
        if (result == null) {
            result = this.externalIndefsToFormulae.get(indef);
            if (result == null) {
                int bits = max.bitLength() + 1;
                List<Formula<None>> resultX;
                resultX = new ArrayList<Formula<None>>(bits);
                // need to handle the flag separately b/c of additional constraints
                infFlag = this.formulaFactory.buildVariable();
                resultX.add(infFlag);
                Formula<None> finite = this.formulaFactory.buildNot(infFlag);
                for (int i = 1; i < bits; ++i) {
                    resultX.add(this.formulaFactory.buildAnd(finite,
                            this.formulaFactory.buildVariable()));
                }

                result = new PolyCircuit(resultX, max);
                this.indefsToVars.put(indef, result);

                // build range/neginf constraint
                if (max.compareTo(BigInteger.valueOf(2).pow(max.bitLength())) < 0) {
                    this.rangeConstraints.add(this.circuitFactory.buildGTCircuit(
                        this.bin(this.intFactory.create(max.add(BigInteger.ONE))),
                        result.getFormulae()));
                }
            }
        }
        return result;
    }

    @Override
    public List<Formula<None>> bin(final T n) {

        if (Globals.useAssertions) {
            assert(!n.isFinite() || n.signum() >= 0) :
                "Cannot binarize negative numbers ("+n+")";
        }

        BigInteger max, value;
        if (n.equals(this.intFactory.zero())) {
            max = BigInteger.ONE;
            value = BigInteger.ZERO;
        } else {
            max = n.getValue();
            value = n.getValue();
        }

        int length = max.bitLength();
        if (length == 0) {
            length = 1;
        }
        List<Formula<None>> formulae = new ArrayList<Formula<None>>(length + 1);
        formulae.add(n.isFinite() ? this.ZERO : this.ONE);  // neginf flag

        for (int i = 0; i < length; ++i) {
            boolean ithBitIsSet = value.testBit(i);
            formulae.add(ithBitIsSet ? this.ONE : this.ZERO);
        }

        return formulae;
    }

    @Override
    public PolyCircuit toCircuit(final T n) {
        if (n == null) {
            return this.one();
        }
        List<Formula<None>> formulae = this.bin(n);
        BigInteger max;
        if (n.equals(this.intFactory.zero()) || n.equals(this.intFactory.one())) {
            max = BigInteger.ONE;
        } else {
            max = n.getValue();
        }
        return new PolyCircuit(formulae, max);
    }

    @Override
    public T toValue(final List<? extends Formula<None>> formulae) {

        if (Globals.useAssertions) {
            assert (formulae.size() <= 31);
        }

        T cachedValue = super.toValue(formulae);
        if (cachedValue != null) {
            return cachedValue;
        }

        Formula<None> negInfFlag = formulae.get(0);
        if (negInfFlag.isConstant()) {
            if (negInfFlag.getGateType() == CircuitGate.TRUE) {
                this.coeffValues.put(formulae, this.intFactory.zero());
                return this.intFactory.zero();
            }
        } else {
            if (this.interpretation.contains(negInfFlag.getId())) {
                this.coeffValues.put(formulae, this.intFactory.zero());
                return this.intFactory.zero();
            }
        }

        int value = 0;
        int twoToTheN = 1;
        for (int i = 1; i < formulae.size(); i++) {
            Formula<None> f = formulae.get(i);
            if (f.isConstant()) {
                // constants don't care about interpretations
                int gateType = f.getGateType();
                if (gateType == CircuitGate.TRUE) {
                    value += twoToTheN;
                }
            } else if (this.interpretation.contains(f.getId())) {
                // variables or non-atomic formulae do care in general, though
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

        T result = this.intFactory.create(value);
        this.coeffValues.put(formulae, result);
        return result;
    }

    /**
     * Build a formula that expresses the statement that at least one
     * variable in each set in finiteOnly has to be interpreted by a
     * value other than negative infinity. Used to ensure the
     * "somewhere finiteness" of the interpretation.
     * @param finiteOnly A set of sets of variable names.
     */
    public Formula<None> getFinitenessConstraints(Set<Set<String>> finiteOnly) {

        List<Formula<None>> conjFormulae =
            new ArrayList<Formula<None>>(finiteOnly.size());
        for (Set<String> ids : finiteOnly) {
            List<Formula<None>> disjFormulae =
                new ArrayList<Formula<None>>(ids.size());
            if (!ids.isEmpty()) {
                for (String varName : ids) {
                    if (Globals.useAssertions) {
                        assert(this.indefsToVars.containsKey(varName));
                    }
                    Formula<None> infFlag =
                        this.indefsToVars.get(varName).getFormulae().get(0);
                    disjFormulae.add(this.formulaFactory.buildNot(infFlag));
                }
            }
            conjFormulae.add(this.formulaFactory.buildOr(disjFormulae));
        }
        return this.formulaFactory.buildAnd(conjFormulae);
    }

    /**
     * Build a formula that expresses the statement that all variables
     * in the given set have to be interpreted by non-negative values.
     * @param mustBePositive A set of variable names.
     */
    public Formula<None> getAbsolutePositivenessConstraints(Set<String> mustBePositive) {

        List<Formula<None>> result = new ArrayList<Formula<None>>(mustBePositive.size());
        boolean hasShift = this.shift > 0;

        // If we are not shifting
        // Otherwise, values are positive iff they are at least equal
        // to the shift (if we shift by n, a value of n means 0).
        List<Formula<None>> offsetFormula = hasShift ?
            this.bin(this.intFactory.create(this.shift - 1)) :
            this.bin(this.intFactory.one()); // here the 'one' element is 0 ;)

        for (String varName : mustBePositive) {
            if (Globals.useAssertions) {
                assert(this.indefsToVars.containsKey(varName));
            }
            List<Formula<None>> indefFmlae = this.indefsToVars.get(varName).getFormulae();
            Formula<None> isPositive;
            if (hasShift) { // a > shift - 1  iff  a - shift >= 0
                isPositive = this.circuitFactory.buildGTCircuit(indefFmlae, offsetFormula);
            } else { // a >= 0, there's no shift (might also use a != -inf?)
                isPositive = this.circuitFactory.buildGECircuit(indefFmlae, offsetFormula).x;
            }
            result.add(isPositive);
        }
        return this.formulaFactory.buildAnd(result);
    }

    /**
     * Build a formula that expresses the statement that all variables
     * in the given set have to be interpreted by non-negative values.
     * @param somewherePositive A set of variable names.
     */
    public Formula<None> getSomewherePositivenessConstraints(Set<Set<String>> somewherePositive) {
        List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(somewherePositive.size());
        boolean hasShift = this.shift > 0;

        // If we are not shifting
        // Otherwise, values are positive iff they are at least equal
        // to the shift (if we shift by n, a value of n means 0).
        List<Formula<None>> offsetFormula = hasShift ?
            this.bin(this.intFactory.create(this.shift - 1)) :
            this.bin(this.intFactory.one()); // here the 'one' element is 0 ;)

        for (Set<String> vars : somewherePositive) {
            if (Globals.useAssertions) {
                assert ! vars.isEmpty();
            }
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(vars.size());
            for (String varName : vars) {
                if (Globals.useAssertions) {
                    assert(this.indefsToVars.containsKey(varName));
                }
                List<Formula<None>> indefFmlae = this.indefsToVars.get(varName).getFormulae();
                Formula<None> isPositive;
                if (hasShift) { // a > shift - 1  iff  a - shift >= 0
                    isPositive = this.circuitFactory.buildGTCircuit(indefFmlae, offsetFormula);
                } else { // a >= 0, there's no shift (might also use a != -inf?)
                    isPositive = this.circuitFactory.buildGECircuit(indefFmlae, offsetFormula).x;
                }
                disjuncts.add(isPositive);
            }
            Formula<None> somewherePosFml = this.formulaFactory.buildOr(disjuncts);
            conjuncts.add(somewherePosFml);
        }
        return this.formulaFactory.buildAnd(conjuncts);
    }

    public void setShift(int shift) {
        this.shift = shift;
    }

    @Override
    public PolyCircuit one() {
        return new PolyCircuit(
                this.bin(this.intFactory.one()), BigInteger.ONE);
    }

    @Override
    public PolyCircuit zero() {
        return new PolyCircuit(
                this.bin(this.intFactory.zero()), BigInteger.ONE);
    }
}
