package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Constructs some predefined Boolean circuits which denote that
 * some circuit node tuples are in certain relations (>, =, >=) or
 * which compute certain arithmetic functions over them (+, *).
 * Note that any List you pass to the methods will be incorporated
 * into the built circuits, so changing the lists or their
 * elements afterwards will change the circuits, too.
 *
 * They are modeled via the same classes that are used for
 * propositional formulae. The only difference between Boolean
 * circuits and formulae is that formulae have a
 * fan-out of at most one (tree style), whereas circuits permit
 * arbitrarily high fan-outs (directed acyclic graph). That way,
 * we can share common subexpressions and achieve a considerable
 * space reduction. Java conveniently allows such a representation
 * by subexpressions being referenced by more than just one node.
 *
 * This variant uses a /unary/ representation of numbers!
 * We have that [1,...,1,0,...0]
 *               ^^^^^^^
 *              k "1"s
 * denotes the natural number k. Note that the number of 0s is arbitrary,
 * so also the empty list is possible. We enforce that if the i-th bit is
 * true, then so is the (i-1)-th bit.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class ArithmeticUnaryCircuitFactory implements ArithmeticFactory {

    private final boolean TRACKING;

    private final FormulaFactory<None> formulaFactory;
    // used for building new circuits

    private final Constant<None> ZERO;
    // shall be used for the constant gates ZERO for circuits produced by this

    private final static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.ArithmeticUnaryCircuitFactory");

    private ArithmeticUnaryCircuitFactory(FormulaFactory<None> formulaFactory,
            PoloSatConfigInfo config) {
        this.formulaFactory = formulaFactory;
        this.ZERO = this.formulaFactory.buildConstant(false);
        this.TRACKING = config.getTracking();
    }

    /**
     * Creates a new ArithmeticCircuitFactory which uses circuitFactory to build
     * circuits.
     *
     * @param circuitFactory the FormulaFactory to be used
     * @param config
     * @return a new ArithmeticCircuitFactory
     */
    public static ArithmeticUnaryCircuitFactory create(FormulaFactory<None> circuitFactory,
            PoloSatConfigInfo config) {
        return new ArithmeticUnaryCircuitFactory(circuitFactory, config);
    }




    /**
     * Builds a circuit which states that xs and ys
     * represent the same number.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a circuit which represents that xs and ys
     *  represent the same number
     */
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

    @Override
    public Formula<None> buildGTCircuit(
            List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        int xsSize = xs.size();
        int ysSize = ys.size();
        int maxSize = Math.max(xsSize, ysSize);

        Formula<None> zero = this.ZERO;
        Formula<None> xIsGreater = zero;
        for (int i = 0; i < maxSize; i++) {
            Formula<None> xi = i >= xsSize ? zero : xs.get(i);
            Formula<None> yi = i >= ysSize ? zero : ys.get(i);
            Formula<None> newTerm = this.formulaFactory.buildAnd(xi,
                    this.formulaFactory.buildNot(yi));
            if (i == 0) {
                xIsGreater = newTerm;
            } else {
                Formula<None> equality = this.formulaFactory.buildIff(xi, yi);
                xIsGreater = this.formulaFactory.buildOr(newTerm,
                        this.formulaFactory.buildAnd(equality, xIsGreater));
            }
        }
        return xIsGreater;
    }


    /**
     * @param xs - the first factor
     * @param ys - the second factor
     * @return
     *  x - circuit for the product of xs and ys<br>
     *  y - the maximum value the product of xs and ys can assume
     */
    @Override
    public PolyCircuit buildTimesCircuit(final PolyCircuit xs, final PolyCircuit ys) {
        List<Formula<None>> zs = this.buildTimesCircuit(xs.getFormulae(), ys.getFormulae());
        if (this.TRACKING) {
            BigInteger zsMax = xs.getMax().multiply(ys.getMax());
            return new PolyCircuit(zs, zsMax);
        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    /**
     * @param xs - the first addend
     * @param ys - the second addend
     * @return
     *  x - circuit for the sum of xs and ys<br>
     *  y - the maximum value the sum of xs and ys can assume
     */
    @Override
    public PolyCircuit buildPlusCircuit(PolyCircuit xs, PolyCircuit ys) {
        List<Formula<None>> zs = this.buildPlusCircuit(xs.getFormulae(), ys.getFormulae());
        if (this.TRACKING) {
            BigInteger zsMax = xs.getMax().add(ys.getMax());
            return new PolyCircuit(zs, zsMax);
        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    /**
     * Builds a circuit that has xs * ys as output, given xs and ys
     * as inputs.
     *
     * @param xs the first addend
     * @param ys ths second addend
     * @return output of a circuit that encodes xs * ys given xs and
     *  ys as inputs
     */
    private List<Formula<None>> buildTimesCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        int xsSize = xs.size();
        int ysSize = ys.size();
        int zsSize = xsSize * ysSize;
        if (zsSize == 0) {
            return Collections.emptyList();
        }
        Formula<None> zero = this.ZERO;
        List<Formula<None>> zs = new ArrayList<Formula<None>>(zsSize);
        for (int i = 1; i <= zsSize; ++i) { // one-based; decrement indices for list access in loop
            List<Formula<None>> disjunctsForZi = new ArrayList<Formula<None>>();
            int ceilSqrtI = AProVEMath.ceilSqrt(i);
            //System.err.print("TIMES: i = "+i+", sqrt(i) = "+ ceilSqrtI + ", pairs: ");
            for (int j = 1; j <= ceilSqrtI; ++j) {
                int k = AProVEMath.ceilDiv(i, j);
                if (j <= k) {
                    List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(2);
                    conjuncts.add(j-1 < xsSize ? xs.get(j-1) : zero);
                    conjuncts.add(k-1 < ysSize ? ys.get(k-1) : zero);
                    Formula<None> d = this.formulaFactory.buildAnd(conjuncts);
                    disjunctsForZi.add(d);
                    //System.err.print("(" + j + "," + k + ") ");
                    if (j != k) { // the mirrored case is needed, too
                        conjuncts = new ArrayList<Formula<None>>(2);
                        conjuncts.add(k-1 < xsSize ? xs.get(k-1) : zero);
                        conjuncts.add(j-1 < ysSize ? ys.get(j-1) : zero);
                        d = this.formulaFactory.buildAnd(conjuncts);
                        disjunctsForZi.add(d);
                        //System.err.print("(" + k + "," + j + ") ");
                    }
                }
            }
            //System.err.println();
            Formula<None> zi = this.formulaFactory.buildOr(disjunctsForZi);
            zs.add(zi);
        }
        return zs;
    }

    /**
     * Builds a circuit that has xs + ys as output, given xs and ys
     * as inputs.
     *
     * @param xs the first addend
     * @param ys ths second addend
     * @return output of a circuit that encodes xs + ys given xs and
     *  ys as inputs
     */
    private List<Formula<None>> buildPlusCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        int xsSize = xs.size();
        int ysSize = ys.size();
        int zsSize = xsSize + ysSize;
        if (zsSize == 0) {
            return Collections.emptyList();
        }
        List<Formula<None>> zs = new ArrayList<Formula<None>>(zsSize);
        Formula<None> zero = this.ZERO;
        for (int i = 1; i <= zsSize; ++i) { // one-based; decrement indices for list access in loop
            //System.err.print("PLUS: i = "+i+", pairs: ");
            List<Formula<None>> binomialTerms = new ArrayList<Formula<None>>();
            for (int j = 0; j <= i; ++j) {
                List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(2);
                if (j == 0) {
                    conjuncts.add(i-1 < xsSize ? xs.get(i-1) : zero);
                    //System.err.print("("+i+",0) ");
                } else if (j == i) {
                    conjuncts.add(j-1 < ysSize ? ys.get(j-1) : zero);
                    //System.err.print("(0,"+j+") ");
                } else {
                    int k = i-j;
                    conjuncts.add(k-1 < xsSize ? xs.get(k-1) : zero);
                    conjuncts.add(j-1 < ysSize ? ys.get(j-1) : zero);
                    //System.err.print("("+k+","+j+") ");
                }
                Formula<None> binomTerm = this.formulaFactory.buildAnd(conjuncts);
                binomialTerms.add(binomTerm);
            }
            //System.err.println();
            Formula<None> zi = this.formulaFactory.buildOr(binomialTerms);
            zs.add(zi);
        }
        return zs;
    }

    /**
     * Convenience method: Builds a circuit which states that xs represents
     * a number that is greater than or equal to the one ys represents.
     *
     * Based on buildGTCircuit and buildEQCircuit.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return x: the output of a circuit that represents "xs >= ys"
     *         y: the output of the subcircuit that represents "xs == ys"
     *            (useful for searchstrict mode)
     */
    @Override
    public Pair<Formula<None>, Formula<None>> buildGECircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {

        // just reduce to the definition: A >= B iff (A > B or A = B)
        final Formula<None> xsGTys = this.buildGTCircuit(xs, ys);
        final Formula<None> xsEQys = this.buildEQCircuit(xs, ys);
        final Formula<None> resultX = this.formulaFactory.buildOr(xsGTys, xsEQys);
        return new Pair<Formula<None>, Formula<None>>(resultX, xsEQys);
    }

    /**
     * Represent 2^xs.
     * @param xs The circuit of the exponent.
     * @return 2^xs.
     */
    @Override
    public PolyCircuit buildPowerOfTwo(PolyCircuit xs) {
        throw new UnsupportedOperationException("Shifts are currently not supported for unary Diophantine encoding.");
    }

    /**
     * @param shiftBy - How many bits to shift? (UNARY value)
     * @param xs - the factor
     * @return
     *  x - circuit for the shift of xs << log(shiftBy)
     *  y - the maximum value the shift can assume
     */
    @Override
    public PolyCircuit buildShiftRightUnary(PolyCircuit shiftBy, PolyCircuit xs) {
        throw new UnsupportedOperationException("Shifts are currently not supported for unary Diophantine encoding.");
    }

    @Override
    public PolyCircuit buildMixedDualAdder(PolyCircuit shiftBy, PolyCircuit xs) {
        throw new UnsupportedOperationException("Shifts / corresponding adders are currently not supported for unary Diophantine encoding.");
    }

    @Override
    public PolyCircuit buildShiftRightBinary(PolyCircuit shiftBy, PolyCircuit xs) {
        throw new UnsupportedOperationException("Shifts are currently not supported for unary Diophantine encoding.");
    }
}
