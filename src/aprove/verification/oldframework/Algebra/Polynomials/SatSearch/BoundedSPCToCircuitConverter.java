package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts sets of SimplePolyConstraints (SPCs) to Boolean circuits.
 * As opposed to propositional formulae, a fan-out > 1 is explicitly
 * desired here.
 *
 * "Bounded" means that we have upper bounds for the bit positions
 * of sums and products where the SAT solver may evaluate to true.
 *
 * See also the paper on Matrix Interpretations for Term Rewriting (IJCAR 06).
 *
 * Important Note:<br>
 * For this to function properly, one has to take care that the
 * overflows of <i>every</i> occurrence of a sub-polynomial are
 * accounted for. This may make caching of PolyCircuits for
 * polynomials more complicated since also the corresponding
 * overflows must be remembered..
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class BoundedSPCToCircuitConverter extends PlainSPCToCircuitConverter {

    // the sideConstraints result from the overall overflow data
    // and will be appended to the resulting formula at the end
    private List<Formula<None>> sideConstraints;

    protected BoundedSPCToCircuitConverter(FormulaFactory<None> formulaFactory,
            Map<String, BigInteger> ranges, BigInteger defaultRange,
            int sumLimit, int productLimit, PoloSatConfigInfo config) {
        super(formulaFactory, ranges, defaultRange, config);
        this.arithmeticFactory = BoundedArithmeticCircuitFactory.create(formulaFactory, sumLimit, productLimit, config);
        this.sideConstraints = new ArrayList<Formula<None>>(2048);
    }

    /**
     * @return a new SimplePolyConstraintsToCircuitConverter which uses bits
     *  propositional vars per indefinite coefficient
     */
    public static BoundedSPCToCircuitConverter create (FormulaFactory<None> formulaFactory,
            Map<String, BigInteger> ranges, BigInteger defaultRange,
            int sumLimit, int productLimit,
            PoloSatConfigInfo config) {
        return new BoundedSPCToCircuitConverter(formulaFactory, ranges,
                defaultRange, sumLimit, productLimit, config);
    }

    /**
     * Converts a set of SimplePolyConstraints and a set of searchstrict
     * SimplePolyConstraints to a Boolean circuit that
     * is satisfiable iff the SimplePolyConstraints are satisfiable
     * over [0 .. 2^bits - 1]. Here, bits is the number of bits this
     * has been created with. Furthermore, a mapping from the
     * indefinite coefficients that occur in the
     * SimplePolyConstraints to lists of propositional variables
     * is computed. By using this mapping, it is possible to obtain
     * a satisfying interpretation for the SimplePolyConstraints from
     * a model of the circuit.
     *
     * @param spcs to be converted
     * @param searchStrictSpcs to be converted; empty indicates
     *  that we are not in searchstrict mode
     * @return a SAT encoding of spcs over the range [0 .. 2^bits - 1]
     */
    @Override
    public Pair<Formula<None>, Map<String, PolyCircuit>> convert(Set<SimplePolyConstraint> spcs,
            Set<SimplePolyConstraint> searchStrictSpcs, Abortion aborter) throws AbortionException {

        // due to the special shape of the searchstrict constraints and
        // their relation to the other top level conjuncts (the polynomials
        // of the searchstrict constraints also occur in the top level
        // conjuncts), we can just attach the side constraints globally
        Pair<Formula<None>, Map<String, PolyCircuit>> resultOfSuper = super.convert(spcs, searchStrictSpcs, aborter);

        // conjunction of negations of all elements of this.overflows
        // (needed for achieving the bounding) along with the formula
        // built by superclass code
        List<Formula<None>> overflows = ((BoundedArithmeticCircuitFactory) this.arithmeticFactory).getOverflows();
        List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(overflows.size() + 1);
        for (Formula<None> overflow : overflows) {
            conjuncts.add(this.formulaFactory.buildNot(overflow));
        }
        conjuncts.add(resultOfSuper.x);
        Formula<None> resultX = this.formulaFactory.buildAnd(conjuncts);
        return new Pair<Formula<None>, Map<String, PolyCircuit>>(resultX, resultOfSuper.y);
    }

    /**
     * Converts a constraint between two SimplePolynomials to a Boolean circuit
     * with just a single output node. Also encodes that the allowed number of
     * bits for the intermediate values is not exceeded.
     *
     * @param left may only contain positive factors
     * @param right may only contain positive factors
     * @param type
     * @param returnEQ states whether the y component of the returned pair should
     *  contain the EQ constraint that corresponds to <code>left</code> and
     *  <code>right</code>.
     * @return x: the output node of the corresponding Boolean circuit<br>
     *         y: returnEQ ? "left == right" : null<br>
     */
    @Override
    protected Pair<Formula<None>, Formula<None>> convertConstraint(SimplePolynomial left,
            SimplePolynomial right, ConstraintType type, boolean returnEQinY) {
        Pair<Formula<None>, Formula<None>> superRes = super.convertConstraint(left, right, type, returnEQinY);
        BoundedArithmeticCircuitFactory baFactory = (BoundedArithmeticCircuitFactory) this.arithmeticFactory;
        List<Formula<None>> negateUsIfConstraintHolds = baFactory.getOverflows();
        baFactory.resetOverflows();

        for (Formula<None> overflowBit : negateUsIfConstraintHolds) {
            Formula<None> f = this.formulaFactory.buildImplication(superRes.x,
                    this.formulaFactory.buildNot(overflowBit));
            this.sideConstraints.add(f);
            if (superRes.y != null) {
                f = this.formulaFactory.buildImplication(superRes.y,
                        this.formulaFactory.buildNot(overflowBit));
                this.sideConstraints.add(f);
            }
        }

        return superRes;
    }

    /**
     * Works like the superclass method, but also encodes that the
     * allowed number of bits for the intermediate values is not exceeded.
     * Moreover, the side constraints held internally are reset.
     */
    @Override
    public Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(final Formula<Diophantine> f,
        final Collection<Formula<Diophantine>> specialSubformulae,
        final Abortion abortion) throws AbortionException {
        final Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> superResult =
            super.convert(f, specialSubformulae, abortion);
        final List<Formula<None>> overallConstraints =
                new ArrayList<Formula<None>>(this.sideConstraints);
        this.sideConstraints = new ArrayList<Formula<None>>();
        overallConstraints.add(superResult.x);
        Formula<None> newResX = this.formulaFactory.buildAnd(overallConstraints);
        return new Quadruple<Map<Formula<Diophantine>, Formula<None>>,
                Formula<None>, Map<String, PolyCircuit>,
                Map<Variable<Diophantine>, Variable<None>>>
                        (superResult.w, newResX, superResult.y, superResult.z);
    }
}
