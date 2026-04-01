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
 * A CircuitFactory for constraints over (positive) exotic integers
 * using unary encoding.
 *
 * This abstract class implements the encoding for equality and
 * multiplication, which are identical for arctic and tropical
 * numbers. Addition and the greater-than relation, which differ,
 * must be implemented in concrete subclasses.
 *
 * Note that for PolyCircuits for exotic (i.e., arctic/tropical) numbers,
 * the first element of PolyCircuit.getFormulae() is the infinity bit.
 * The value PolyCircuit.getMax() denotes the maximum <i>finite</i>
 * value the circuit may assume by construction. (Actually this is not
 * all /that/ useful for unary circuits since these are tailor-made to
 * fit the maximum values precisely, but does not do much harm either.)
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class ExoticIntUnaryCircuitFactory<T extends ExoticInt<T>> extends CircuitFactory {

    // for a bitvector (a_k, ..., a_1 ; a_0) encoding a compound expression,
    // require explicitly that a_k -> a_{k-1}, ..., a_2 -> a_1 must hold?
    protected static final boolean requirePrefixForTimes = false;
    protected static final boolean requirePrefixForPlus = false;

    protected ExoticIntUnarizer<T> unarizer = null;

    public ExoticIntUnaryCircuitFactory(FormulaFactory<None> formulaFactory) {
        super(formulaFactory);
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
    public Formula<None> buildEQCircuit(List<? extends Formula<None>> xs, List<? extends Formula<None>> ys) {

        int xsSize = xs.size();
        int ysSize = ys.size();

        // wlog: ys should be at least as long as xs
        if (xsSize > ysSize) {
            List<? extends Formula<None>> tmpFmlae = xs;
            xs = ys;
            ys = tmpFmlae;

            int tmpSize = xsSize;
            xsSize = ysSize;
            ysSize = tmpSize;
        }


        List<Formula<None>> comparisons = new ArrayList<Formula<None>>(ysSize);
        Formula<None> xi, yi;
        for (int i = 0; i < xsSize; i++) {
            // values should be the same
            xi = xs.get(i);
            yi = ys.get(i);
            comparisons.add(this.formulaFactory.buildIff(xi, yi));
        }

        for (int i = xsSize; i < ysSize; i++) {
            // If ys exceeds xs, then we need a 0 in the exceeding position,
            // otherwise the numbers are different.
            yi = ys.get(i);
            comparisons.add(this.formulaFactory.buildNot(yi));
        }

        return this.formulaFactory.buildAnd(comparisons);
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
        int xfsSize = xfs.size();
        int yfsSize = yfs.size();

        if (Globals.useAssertions) {
            assert(xfsSize >= 1);
            assert(yfsSize >= 1);
        }

        BigInteger zMax = xs.getMax().add(ys.getMax());
        int length = zMax.intValue();
        List<Formula<None>> zs = new ArrayList<Formula<None>>(length + 1);

        Formula<None> xFlag = xfs.get(0);
        Formula<None> yFlag = yfs.get(0);
        Formula<None> zFlag = this.formulaFactory.buildOr(xFlag, yFlag);
        zs.add(zFlag);
        Formula<None> zIsFinite = this.formulaFactory.buildNot(zFlag);
        Formula<None> one = this.formulaFactory.buildConstant(true);
        Formula<None> oldZi = null;
        for (int i = 1; i <= length; i++) {
            List<Formula<None>> binomialTerms = new ArrayList<Formula<None>>();
            for (int j = 0; j <= i; j++) {
                if ((j < xfsSize || j <= 0) && ((i-j) < yfsSize || i <= j)) {
                    Formula<None> xj = j > 0 ? xfs.get(j) : one;
                    Formula<None> yk = i > j ? yfs.get(i-j) : one;
                    binomialTerms.add(this.formulaFactory.buildAnd(xj, yk));
                }
            }
            Formula<None> newZi;
            if (ExoticIntUnarizer.singleInfFlagImplication) {
                newZi = this.formulaFactory.buildOr(binomialTerms);
                if (i == 1) {
                    this.unarizer.addGlobalConstraint(this.formulaFactory.buildImplication(newZi, zIsFinite));
                }
                zs.add(newZi);
            } else {
                newZi = this.formulaFactory.buildAnd(zIsFinite,
                            this.formulaFactory.buildOr(binomialTerms));
                zs.add(newZi);
            }

            // try out imposing prefix condition also for the results here
            if (ExoticIntUnaryCircuitFactory.requirePrefixForTimes) {
                if (oldZi != null) {
                    Formula<None> prefixCond =
                        this.formulaFactory.buildImplication(newZi, oldZi);
                    this.unarizer.addGlobalConstraint(prefixCond);
                }
                oldZi = newZi;
            }
        }

        return new PolyCircuit(zs, zMax);
    }

    /**
     * Exotic addition (ie. min/max operations) have no inverse,
     * hence there is no exotic subtraction.
     * If this method is ever called, you're doing something wrong.
     */
    @Override
    @Deprecated
    public PolyCircuit buildMinusCircuit(PolyCircuit xs, PolyCircuit ys) {
        throw new UnsupportedOperationException("Cannot subtract arctic/tropical integers");
    }

    /**
     * Experimental code to allow for keeping global side constraints
     * in the unarizer.
     *
     * @param unarizer
     */
    public void setUnarizer(ExoticIntUnarizer<T> unarizer) {
        this.unarizer = unarizer;
    }
}
