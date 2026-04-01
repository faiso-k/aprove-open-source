package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Converts variables of type C into a binary representation for
 * SAT solving and computes values for them when given a
 * solution (i.e. a map of values for the binarized variables).
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class Binarizer<C extends GPolyCoeff> {

    /**
     * Assign a PolyCircuit to each indefinite coefficient known to occur.
     */
    protected final Map<String, PolyCircuit> indefsToVars;

    /**
     * Do so also for externalIndefsToVars that have been put by the user.
     * We assume that the values the SAT solver finds for them are not
     * interesting for the user.
     */
    protected final Map<String, PolyCircuit> externalIndefsToFormulae;

    /**
     * To be used for building the range constraints.
     */
    protected final CircuitFactory circuitFactory;

    /**
     * To be used for getting the constants ZERO and ONE and
     * new propositional variables
     */
    protected final FormulaFactory<None> formulaFactory;

    /**
     * An interpretation of bit variables computed by a SAT solver.
     * Used for computing the actual values of binarized variables.
     */
    protected Set<Integer> interpretation = null;

    /**
     * A cache for values already computed once.
     */
    protected Map<List<? extends Formula<None>>, C> coeffValues;

    /**
     * A set of constraints that restrict the maximal values of binarized variables.
     */
    protected List<Formula<None>> rangeConstraints;

    // cache the constants, they are used rather often
    protected final Constant<None> ZERO;
    protected final Constant<None> ONE;

    public Binarizer(CircuitFactory circuitFactory) {
        this.indefsToVars = new LinkedHashMap<String, PolyCircuit>(128);
        this.externalIndefsToFormulae = new HashMap<String, PolyCircuit>(128);
        this.coeffValues = new HashMap<List<? extends Formula<None>>, C>();
        this.rangeConstraints = new ArrayList<Formula<None>>();
        // feel free to change the initial sizes to better values.

        this.circuitFactory = circuitFactory;
        this.formulaFactory = circuitFactory.getFormulaFactory();
        this.ZERO = this.formulaFactory.buildConstant(false);
        this.ONE = this.formulaFactory.buildConstant(true);
    }

    /**
     * @return the internal map from indefinite coefficients
     *  to propositional variables; <b>modify it only if you
     *  know what you are doing!</b>
     */
    public Map<String, PolyCircuit> getIndefsToVars() {
        return this.indefsToVars;
    }

    /**
     * @param indef - indefinite for which we want to add a
     *  propositional representation.
     * @param pc - the propositional representation of indef
     */
    public void put(String indef, PolyCircuit pc) {
        this.externalIndefsToFormulae.put(indef, pc);
    }

    /**
     * Returns the corresponding representation of an indefinite coefficient
     * of a polynomial which consists of <code>bits</code> propositional
     * variables. For a given indefinite, the result will always be the same
     * (it will be cached once it has been computed), so the value of bits
     * passed to bin should be constant for a given value of indef.
     *
     * TODO introduce facility for setting certain positions of the
     *      result to ZERO or ONE (e.g. by masking)
     *
     * @param indef the indefinite to be represented in propositional logic
     * @param range the maximum value of the indefinite
     * @return the representation of <code>indef</code> by <code>bits</code>
     *  propositional variables
     */
    abstract public PolyCircuit bin(String indef, C range);

    /**
     * @param n to be represented as a binary in propositional logic
     * @return the binary representation of <code>n</code> in
     *  propositional logic
     */
    abstract public List<Formula<None>> bin(final C n);

    /**
     * @param n
     * @return a circuit representing the constant n.
     */
    abstract public PolyCircuit toCircuit(final C n);

    /**
     * Pass the SAT solver's result to the binarizer in order to
     * compute coefficient values.
     */
    public void setInterpretation(int[] model) {
        // x \in interpretation <=> x |-> true
        this.interpretation = new HashSet<Integer>(model.length);
        for (int i = 0; i < model.length; ++i) {
            if (model[i] > 0) {
                this.interpretation.add(model[i]);
            }
        }
    }

    /**
     * Compute the result of a coefficient. Of course, setInterpretation()
     * must have been called beforehand.
     *
     * @param formulae the set of formulae representing the coefficient.
     * @return the value of the coefficient.
     */
    public C toValue(final List<? extends Formula<None>> formulae) {
        if (Globals.useAssertions) {
            assert(this.interpretation != null);
        }
        if (this.coeffValues.containsKey(formulae)) {
            return this.coeffValues.get(formulae);
        } else {
            return null;
        }
    }

    /**
     * @return a mapping from all binarized variables to their SAT-obtained values.
     */
    public Map<GPolyVar, C> getSubstitution() {
        Map<GPolyVar, C> substitution =
            new LinkedHashMap<GPolyVar, C>(this.indefsToVars.size());
        for (String varName : this.indefsToVars.keySet()) {
            List<Formula<None>> formulae = this.indefsToVars.get(varName).getFormulae();
            substitution.put(GAtomicVar.createVariable(varName),
                    this.toValue(formulae));
        }
        return substitution;
    }

    public Formula<None> getRangeConstraint() {
        return this.formulaFactory.buildAnd(this.rangeConstraints);
    }

    /**
     * @return a PolyCircuit representing the neutral element of multiplication.
     */
    abstract public PolyCircuit one();

    /**
     * @return a PolyCircuit representing the neutral element of addition,
     * which should also be the 0-element of multiplication.
     */
    abstract public PolyCircuit zero();

    public FormulaFactory<None> getFormulaFactory() {
        return this.formulaFactory;
    }
}
