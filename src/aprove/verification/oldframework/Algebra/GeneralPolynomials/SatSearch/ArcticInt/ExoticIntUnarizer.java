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
 * A binarizer for (positive) exotic integers that uses unary encoding.
 *
 * Exotic numbers are represented by means of a flag bit, which is 1
 * iff the number is (negative) infinity, and a string of 1s equal in
 * length to the number.
 *
 * Since both arctic and tropical integers are treated completely
 * analogously, this code is able to handle both types.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ExoticIntUnarizer<T extends ExoticInt<T>> extends ExoticIntBinarizer<T> {

    // true:  ||a|| = (a_n, ..., a_1; a_0) with
    //        global constraints  a_n -> a_{n-1}, ..., a_2 -> a_1, a_1 -> !a_0
    //
    // false: ||a|| = (a_n and !a_0, ..., a_1 and !a_0; a_0) with
    //        global constraints  a_n -> a_{n-1}, ..., a_2 -> a_1,
    //
    // Note that "true" is incomplete -- just think about "times(b, c)"
    // where b = -\infty and c = 1; then the lowest finite bit is
    // b_1 OR c_1, viz. 1; but the resulting value is still -\infty;
    // so it really is necessary to make the connection of the
    // infinity flag with each finite position explicit
    public static final boolean singleInfFlagImplication = false;

    // true: a_i AND finite  ->  a_{i-1} AND finite
    // false; a_i -> a_{i-1}
    public static final boolean infFlagInPrefixCond = false;

    protected List<Formula<None>> prefixConditions =
        new ArrayList<Formula<None>>();

    public ExoticIntUnarizer(
            final ExoticIntFactory<T> intFactory,
            final CircuitFactory circuitFactory) {
        super(intFactory, circuitFactory);
    }

    @Override
    public PolyCircuit bin(final String indef, final T range) {

        BigInteger max;
        Formula<None> infFlag;

        if (Globals.useAssertions) {
            assert (indef != null);
        }

        if (range.equals(this.intFactory.zero()) || range.equals(this.intFactory.one())) {
            max = BigInteger.ZERO;
        } else {
            max = range.getValue();
        }
        max = max.add(BigInteger.valueOf(this.shift));

        PolyCircuit result = this.indefsToVars.get(indef);
        if (result == null) {
            result = this.externalIndefsToFormulae.get(indef);
            if (result == null) {
                final int maxInt = max.intValue();
                List<Formula<None>> resultX;
                resultX = new ArrayList<Formula<None>>(maxInt + 1);
                // need to handle the flag separately b/c of additional constraints
                infFlag = this.formulaFactory.buildVariable();
                Formula<None> finite = this.formulaFactory.buildNot(infFlag);
                resultX.add(infFlag);
                Formula<None> x = null;
                for (int i = 0; i < maxInt; ++i) {
                    Formula<None> newX = this.formulaFactory.buildVariable();
                    if (ExoticIntUnarizer.singleInfFlagImplication) {
                        resultX.add(newX);
                    } else {
                        Formula<None> resXi = this.formulaFactory.buildAnd(finite, newX);
                        resultX.add(resXi);
                        if (ExoticIntUnarizer.infFlagInPrefixCond) {
                            newX = resXi; // for the prefix conditions
                        }
                    }
                    if (x != null) {
                        this.prefixConditions.add(this.formulaFactory.buildImplication(newX, x));
                    } else if (ExoticIntUnarizer.singleInfFlagImplication) { // a_1 -> not -\infty
                        this.prefixConditions.add(this.formulaFactory.buildImplication(newX, finite));
                    }
                    x = newX;
                }

                result = new PolyCircuit(resultX, max);
                this.indefsToVars.put(indef, result);
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

        int value = n.isFinite() ? n.getValue().intValue() : 0;

        List<Formula<None>> formulae = new ArrayList<Formula<None>>(value + 1);
        formulae.add(n.isFinite() ? this.ZERO : this.ONE);  // neginf flag

        for (int i = 0; i < value; ++i) {
            formulae.add(this.ONE);
        }

        return formulae;
    }

    @Override
    public PolyCircuit toCircuit(final T n) {
        if (n == null) {
            return this.one();
        }
        return new PolyCircuit(this.bin(n), n.getValue());
    }

    @Override
    public T toValue(final List<? extends Formula<None>> formulae) {

        /*T cachedValue = super.toValue(formulae);
        if (cachedValue != null) {
            return cachedValue;
        }*/

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
        int size = formulae.size();
        for (int i = 1; i < size; i++) {
            Formula<None> f = formulae.get(i);
            if (f.isConstant()) {
                if (f.getGateType() == CircuitGate.TRUE) {
                    ++value;
                } else {
                    if (Globals.useAssertions) {
                        IndefiniteUnarizer.assertPrefixCondition(formulae, this.interpretation, i, size);
                    }
                    break; // prefix condition
                }
            } else if (f.getId() == AbstractFormula.ID_UNSET) {
                // some formulae do not get to enter the actual CNF encoding,
                // so there is no Tseitin variable for them; get their truth
                // values in the classic style (if some actual variables of
                // theirs did not make it to the CNF either, it means that
                // their truth value does not matter overall, and we can
                // safely assume them to be 'false'
                if (f.interpret(this.interpretation)) {
                    ++value;
                } else {
                    if (Globals.useAssertions) {
                        IndefiniteUnarizer.assertPrefixCondition(formulae, this.interpretation, i, size);
                    }
                    break; // prefix condition
                }
            } else if (this.interpretation.contains(f.getId())) {
                ++value;
            } else {
                if (Globals.useAssertions) {
                    IndefiniteUnarizer.assertPrefixCondition(formulae, this.interpretation, i, size);
                }
                break;  // prefix condition
            }
        }

        T result = this.intFactory.create(value);
        this.coeffValues.put(formulae, result);
        return result;
    }

    /**
     * Adds <code>global</code> to the subformulas that must be satisfied
     * for the overall formula to be satisfied.
     *
     * @param global - non-null
     */
    public void addGlobalConstraint(Formula<None> global) {
        // slightly hackish, I guess
        this.prefixConditions.add(global);
    }

    /**
     * Return a formula that states that if a bit vector's i-th bit is set,
     * then all bits below must be set, too.
     */
    public Formula<None> getPrefixCondition() {
        return this.formulaFactory.buildAnd(this.prefixConditions);
    }
}
