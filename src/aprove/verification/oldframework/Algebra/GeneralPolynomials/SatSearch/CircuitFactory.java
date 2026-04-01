package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A factory to create PolyCircuits. The actual operations must be
 * implemented in subclasses for every type of coefficient specifically.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class CircuitFactory {

    protected final FormulaFactory<None> formulaFactory;

    /**
     * Creates a new circuit factory.
     * @param formulaFactory a factory to build propositional formulae.
     */
    public CircuitFactory(
            final FormulaFactory<None> formulaFactory) {
        this.formulaFactory = formulaFactory;
    }

    /**
     * Builds a Boolean circuit that encodes that xs
     * represents a strictly greater number than ys.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a formula that encodes that xs > ys
     */
    abstract public Formula<None> buildGTCircuit(
            List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys);

    /**
     * Builds a circuit which states that xs and ys
     * represent the same number.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a circuit which represents that xs and ys
     *  represent the same number
     */
    abstract public Formula<None> buildEQCircuit(
            List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys);

    /**
     * Convenience method: Builds a circuit which states that xs represents
     * a number that is greater than or equal to the one ys represents. You
     * may have to overwrite this method for orderings where
     * xs >= ys != xs > ys || xs = ys.
     *
     * Based on buildGTCircuit and buildEQCircuit.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return x: the output of a circuit that represents "xs >= ys"
     *         y: the output of the subcircuit that represents "xs == ys"
     *            (useful for searchstrict mode)
     */
    public Pair<Formula<None>, Formula<None>> buildGECircuit(
            List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {

        // just reduce to the definition: A >= B iff (A > B or A = B)
        Formula<None> xsGTys = this.buildGTCircuit(xs, ys);
        Formula<None> xsEQys = this.buildEQCircuit(xs, ys);
        Formula<None> resultX = this.formulaFactory.buildOr(xsGTys, xsEQys);
        return new Pair<Formula<None>, Formula<None>>(resultX, xsEQys);
    }

    /**
     * @param f1
     * @param f2
     * @param f3
     * @return a formula/circuit which is satisfied by exactly those
     *  interpretations that satisfy at least 2 of the arguments
     */
    public Formula<None> build2or3Circuit(Formula<None> f1, Formula<None> f2, Formula<None> f3) {
        Formula<None> pos0, pos1, pos2;
        pos0 = this.formulaFactory.buildOr(f1, f2);
        pos1 = this.formulaFactory.buildOr(f1, f3);
        pos2 = this.formulaFactory.buildOr(f2, f3);
        return this.formulaFactory.buildAnd(pos0, pos1, pos2);
    }

    /**
     * Build a circuit that encodes xs + ys (for whatever operation `+` defined
     * on C).
     * @param xs
     * @param ys
     */
    abstract public PolyCircuit buildPlusCircuit(
            final PolyCircuit xs,
            final PolyCircuit ys);

    /**
     * Build a circuit that encodes xs - ys (for whatever operation `-` defined
     * on C, if any).
     * @param xs
     * @param ys
     */
    abstract public PolyCircuit buildMinusCircuit(
            final PolyCircuit xs,
            final PolyCircuit ys);

    /**
     * Build a circuit that encodes xs * ys (for whatever operation `*` defined
     * on C).
     * @param xs
     * @param ys
     */
    abstract public PolyCircuit buildTimesCircuit(
            final PolyCircuit xs,
            final PolyCircuit ys);

    public FormulaFactory<None> getFormulaFactory() {
        return this.formulaFactory;
    }

    /**
     * @return whether this uses bounded arithmetic (which means that you
     *  need to take care of setting the overflow bits to ZERO);
     *  defaults to false -- should return true iff this is an instance of
     *  BoundedCircuitFactory
     */
    public boolean usesBoundedArithmetic() {
        return false;
    }
}
