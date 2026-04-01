package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * Generates a PolyCircuit that represents a GPoly over C.<br>
 * This class is completely generic, you just need to
 * plug in a binarizer and a CircuitFactory for C.
 *
 * Makes (and asserts) the assumption that MinusNodes only
 * occur to represent the ZERO element of the semiring via
 * minus(ONE, ONE).
 *
 * @param <C> The type of the polynomial's coefficients.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PolyToCircuitConverter<C extends GPolyCoeff,
        V extends GPolyVar> extends GPolyVisitor<C, V> {

    /**
     * Used to create binary representations of the variables and
     * constants (if any) in the polynomials.
     */
    private final Binarizer<C> binarizer;

    /**
     * Used to create circuits.
     */
    private final CircuitFactory circuitFactory;

    /**
     * Do we use bounded arithmetic (and must thus include information
     * on the overflows that must become false for the PolyCircuit to
     * actually represent the polynomial)?
     */
    private final boolean useBoundedArithmetic;

    /**
     * If we use bounded arithmetic, it makes sense to keep a reference
     * to the circuit factory casted correspondingly.
     */
    private final BoundedCircuitFactory bcf;


    /**
     * A cache for sub-circuits. Used to retrieve information about sub-nodes,
     * and prevent multiple generation of identical circuits.
     */
    private Map<GPoly<C, V>, Pair<PolyCircuit, Overflows>> circuitCache;

    /**
     * The range (max value) of the variables.
     */
    private final C defaultRange;

    /**
     * During the generation process, this always holds the circuit corresponding
     * to the last visited node. Thus, when the process is finished, it holds the
     * one corresponding to the topmost node, i.e. the whole polynomial.
     */
    private Pair<PolyCircuit, Overflows> circuitWithOverflows;

    private Map<V, C> ranges;

    /**
     * Create a new PolyToCircuitConverter.
     * @param circuitFactory A factory for PolyCircuits over C.
     * @param binarizer A binarizer for coefficients of type C.
     * @param defaultRange The maximum value variables may assume.
     */
    public PolyToCircuitConverter(
            final CircuitFactory circuitFactory,
            final Binarizer<C> binarizer,
            final C defaultRange) {
        this(circuitFactory, binarizer, new HashMap<V, C>(), defaultRange);
    }

    /**
     * Create a new PolyToCircuitConverter.
     * @param circuitFactory A factory for PolyCircuits over C.
     * @param binarizer A binarizer for coefficients of type C.
     * @param defaultRange The maximum value variables may assume.
     */
    public PolyToCircuitConverter(
            final CircuitFactory circuitFactory,
            final Binarizer<C> binarizer,
            final Map<V, C> ranges,
            final C defaultRange) {
        this.circuitFactory = circuitFactory;
        this.useBoundedArithmetic = circuitFactory.usesBoundedArithmetic();
        this.bcf = this.useBoundedArithmetic ?
                (BoundedCircuitFactory) this.circuitFactory : null;
        this.binarizer = binarizer;
        this.ranges = ranges;
        this.defaultRange = defaultRange;
        this.circuitCache = new HashMap<GPoly<C,V>, Pair<PolyCircuit, Overflows>>();
    }

    /**
     * Create a circuit representing a Concat node (i.e., a monomial).
     * This is the product of the coefficient and all variables occurring in the node.
     * @param c Some ConcatNode.
     * @return c.
     */
    @Override
    public GPoly<C, V> caseConcatNode(
            final ConcatNode<C, V> c) {
        Pair<PolyCircuit, Overflows> cachedValue = this.circuitCache.get(c);
        if (cachedValue == null) {
            // TODO optimizations for products of 2
            PolyCircuit temp = this.binarizer.toCircuit(c.getCoeff());
            Map<V, Integer> vars = c.getVariablesWithExponents();
            for (Entry<V, Integer> varToExp : vars.entrySet()) {
                V var = varToExp.getKey();
                int exp = varToExp.getValue();
                C varRange = this.ranges.get(var);
                if (varRange == null) {
                    varRange = this.defaultRange;
                }
                // TODO use repeated binary squaring instead of comb
                for (int i = 1; i <= exp; i++) {
                    temp = this.circuitFactory.buildTimesCircuit(temp,
                            this.binarizer.bin(var.getName(), varRange));
                }
            }
            if (Globals.useAssertions) {
                assert(temp != null);
            }
            Overflows of;
            if (this.useBoundedArithmetic) {
                of = this.bcf.getOverflows();
                this.bcf.reset();
            }
            else {
                of = Overflows.NO_OVERFLOWS;
            }
            Pair<PolyCircuit, Overflows> pcWithOverflows =
                new Pair<PolyCircuit, Overflows>(temp, of);
            this.circuitCache.put(c, pcWithOverflows);
            this.circuitWithOverflows = pcWithOverflows;
        } else {
            this.circuitWithOverflows = cachedValue;
        }
        return c;
    }

    /**
     * Create a circuit representing a Plus node, i.e., the sum of
     * the node's children.
     * @param p Some PlusNode.
     * @param left The left child.
     * @param right The right child.
     * @return p.
     */
    @Override
    public GPoly<C, V> casePlusNode(
            final PlusNode<C, V> p,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        Pair<PolyCircuit, Overflows> cachedValue = this.circuitCache.get(p);
        if (cachedValue == null) {
            Pair<PolyCircuit, Overflows> leftCircuit = this.circuitCache.get(left);
            Pair<PolyCircuit, Overflows> rightCircuit = this.circuitCache.get(right);
            PolyCircuit sum = this.circuitFactory.buildPlusCircuit(leftCircuit.x, rightCircuit.x);
            Overflows sumOf;
            if (this.useBoundedArithmetic) {
                Overflows newOf = this.bcf.getOverflows();
                this.bcf.reset();
                sumOf = Overflows.merge(leftCircuit.y, rightCircuit.y, newOf);
            }
            else {
                sumOf = Overflows.NO_OVERFLOWS;
            }
            Pair<PolyCircuit, Overflows> pcWithOverflows =
                    new Pair<PolyCircuit, Overflows>(sum, sumOf);
            this.circuitCache.put(p, pcWithOverflows);
            this.circuitWithOverflows = pcWithOverflows;
        } else {
            this.circuitWithOverflows = cachedValue;
        }
        return p;
    }

    /**
     * Create a circuit representing a Minus node, i.e., the difference
     * of the node's children. This is possible only if the coefficients
     * support subtraction, resp. if the CircuitFactory does.
     *
     * Current state: No known factory does, so we make (and assert)
     * the assumption that MinusNodes only occur to represent the
     * ZERO element of the semiring via minus(ONE, ONE).
     *
     * @param m Some MinusNode.
     * @param left The left child.
     * @param right The left child.
     * @return m.
     */
    @Override
    public GPoly<C, V> caseMinusNode(
            final MinusNode<C, V> m,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        if (Globals.useAssertions) {
            assert left.isOne();
            assert right.isOne();
        }
        Formula<None> zeroFormula = this.circuitFactory.getFormulaFactory().buildConstant(false);
        List<Formula<None>> zeroTuple = Collections.<Formula<None>>singletonList(zeroFormula);
        PolyCircuit pc = new PolyCircuit(zeroTuple, BigInteger.ZERO);
        this.circuitWithOverflows = new Pair<PolyCircuit, Overflows>(pc, Overflows.NO_OVERFLOWS);
        return m;
    }

    /**
     * Create a circuit representing a Times node, i.e., the product of
     * the node's children.
     * @param t Some TimesNode.
     * @param left The left child.
     * @param right The right child.
     * @return t.
     */
    @Override
    public GPoly<C, V> caseTimesNode(
            final TimesNode<C, V> t,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        Pair<PolyCircuit, Overflows> cachedValue = this.circuitCache.get(t);
        if (cachedValue == null) {
            Pair<PolyCircuit, Overflows> leftCircuit = this.circuitCache.get(left);
            Pair<PolyCircuit, Overflows> rightCircuit = this.circuitCache.get(right);
            PolyCircuit product = this.circuitFactory.buildTimesCircuit(leftCircuit.x, rightCircuit.x);
            Overflows productOf;
            if (this.useBoundedArithmetic) {
                Overflows newOf = this.bcf.getOverflows();
                this.bcf.reset();
                productOf = Overflows.merge(leftCircuit.y, rightCircuit.y, newOf);
            }
            else {
                productOf = Overflows.NO_OVERFLOWS;
            }
            Pair<PolyCircuit, Overflows> pcWithOverflows =
                    new Pair<PolyCircuit, Overflows>(product, productOf);
            this.circuitCache.put(t, pcWithOverflows);
            this.circuitWithOverflows = pcWithOverflows;
        } else {
            this.circuitWithOverflows = cachedValue;
        }
        return t;
    }

    /**
     * Call this after visiting a polynomial to obtain the circuit
     * that was generated from it.
     */
    public Pair<PolyCircuit, Overflows> getCircuitWithOverflows() {
        return this.circuitWithOverflows;
    }

    /**
     * @return the factory used by this visitor.
     */
    public CircuitFactory getFactory() {
        return this.circuitFactory;
    }

    /**
     * @return the binarizer used by this visitor.
     */
    public Binarizer<C> getBinarizer() {
        return this.binarizer;
    }
}
