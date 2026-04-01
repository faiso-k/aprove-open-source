package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.ArcticInt;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.Nat.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A CircuitFactory for constraints over (positive) exotic integers.
 *
 * This abstract class implements the encoding for equality and
 * multiplication, which are identical for arctic and tropical
 * numbers. Addition and the greater-than relation, which differ,
 * must be implemented in concrete subclasses.
 *
 * Note that for PolyCircuits for exotic (i.e., arctic/tropical) numbers,
 * the first element of PolyCircuit.getFormulae() is the infinity bit.
 * The value PolyCircuit.getMax() denotes the maximum <i>finite</i>
 * value the circuit may assume by construction.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class ExoticIntCircuitFactory<T extends ExoticInt<T>> extends CircuitFactory {

    // if set, we also enforce that the encoding of a times b will have
    // all its finite bits set to false if its infinite bit is set to true
    // (if unset, cases like -oo times 1 will have a set finite bit
    private static final boolean enforceInfinityImpliesZeroForTimes = true;

    // keep track of max values for times operation (which may lead to excess
    // bits equivalent to false)
    private static final boolean tracking = true;

    // "keep it simple, stupid" equality checking -- all bits must be equal!
    // (otherwise a difference in the finite bits is allowed, which does not require
    // enforceInfinityImpliesZeroForTimes to be set)
    private static final boolean kissEQ = true;

    /**
     * After removing the sign flag, circuits representing ExoticInts
     * can be handled just like those representing actual natural numbers,
     * which is why we can defer some implementation work to this factory.
     */
    protected final NatCircuitFactory natCircuitFactory;

    public ExoticIntCircuitFactory(FormulaFactory<None> formulaFactory) {
        super(formulaFactory);
        this.natCircuitFactory = new NatCircuitFactory(formulaFactory);
    }

    /**
     * Builds a circuit that encodes that xs represents a
     * greater value than ys.
     * @param xs A list of propositional formulae encoding an
     * exotic integer (variable or number).
     * @param ys Ditto.
     */
    @Override
    abstract public Formula<None> buildGTCircuit(
            final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys);

    @Override
    public Formula<None> buildEQCircuit(final List<? extends Formula<None>> xs, final List<? extends Formula<None>> ys) {

        if (ExoticIntCircuitFactory.kissEQ && ExoticIntCircuitFactory.enforceInfinityImpliesZeroForTimes) {
            return this.natCircuitFactory.buildEQCircuit(xs, ys);
        } else {
            Formula<None> xFlag = xs.get(0);
            Formula<None> yFlag = ys.get(0);
            Formula<None> bothInfinite = this.formulaFactory.buildAnd(xFlag, yFlag);
            Formula<None> neitherInfinite = this.formulaFactory.buildAnd(
                    this.formulaFactory.buildNot(xFlag), this.formulaFactory.buildNot(yFlag));
            Formula<None> valuesAreEqual = this.natCircuitFactory.buildEQCircuit(
                    xs.subList(1, xs.size()), ys.subList(1, ys.size()));
            return this.formulaFactory.buildOr(bothInfinite,
                    this.formulaFactory.buildAnd(neitherInfinite, valuesAreEqual));
        }
    }

    /**
     * Build a circuit that encodes the exotic multiplication of xs and ys.
     * This is dependent from the actual exotic type.
     * @param xs A list of propositional formulae encoding an
     * exotic integer (variable or number).
     * @param ys Ditto.
     */
    @Override
    abstract public PolyCircuit buildPlusCircuit(final PolyCircuit xs, final PolyCircuit ys);

    /**
     * Build a circuit that encodes `xs + ys` (arctic/tropical multiplication).
     * @param xs A list of propositional formulae encoding an
     * exotic integer (variable or number).
     * @param ys Ditto.
     */
    @Override
    public PolyCircuit buildTimesCircuit(PolyCircuit xs, PolyCircuit ys) {

        List<Formula<None>> xfs = xs.getFormulae();
        List<Formula<None>> yfs = ys.getFormulae();

        BigInteger zMax = xs.getMax().add(ys.getMax());
        int length = zMax.bitLength();
        List<Formula<None>> zs = new ArrayList<Formula<None>>(length + 1);

        Formula<None> xFlag = xfs.get(0);
        Formula<None> yFlag = yfs.get(0);
        Formula<None> resFlag = this.formulaFactory.buildOr(xFlag, yFlag);
        zs.add(resFlag);

        List<Formula<None>> resFinitePart;
        if (ExoticIntCircuitFactory.enforceInfinityImpliesZeroForTimes && ExoticIntCircuitFactory.tracking) {
            PolyCircuit xsFinite = xs.toFinitePolyCircuit();
            PolyCircuit ysFinite = ys.toFinitePolyCircuit();

            // tracking! (as in SAT'07)
            PolyCircuit resFinitePolyCircuit
                = this.natCircuitFactory.buildPlusCircuit(xsFinite, ysFinite);
            resFinitePart = resFinitePolyCircuit.getFormulae();

            // implication! such redundant information is helpful
            // (cf. Koprowski, Waldmann, 2008).
            int resFiniteLength = resFinitePart.size();
            Formula<None> finite = this.formulaFactory.buildNot(resFlag);
            for (int i = 0; i < resFiniteLength; ++i) {
                Formula<None> resFiniteI = resFinitePart.get(i);
                zs.add(this.formulaFactory.buildAnd(finite,
                        resFiniteI));
            }
        }
        else { // state up to September 2011
            resFinitePart = this.natCircuitFactory.buildPlusCircuit(
                    xfs.subList(1, xfs.size()), yfs.subList(1, yfs.size()));
            zs.addAll(resFinitePart);
        }
        return new PolyCircuit(zs, zMax);
    }

    /**
     * Exotic addition (ie. min/max operations) have no inverse,
     * hence there is no exotic subtraction.
     * If this method is ever called, you're doing something wrong.
     */
    @Override
    public PolyCircuit buildMinusCircuit(PolyCircuit xs, PolyCircuit ys) {
        throw new UnsupportedOperationException("Cannot subtract arctic/tropical integers");
    }
}
