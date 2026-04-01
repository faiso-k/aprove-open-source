package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Instances of IndefiniteUnarizer are used to convert between
 * indefinite coefficients of polynomials and PolyCircuits.
 * PolyCircuits that encode indefinites are stored once they have
 * been generated so that the <code>bin</code> method can be invoked
 * with one and the same argument for several times. This behavior
 * also allows for the reverse conversion.
 *
 * Furthermore, there are static methods for obtaining propositional
 * tuples from natural numbers and for obtaining the number encoded
 * by a tuple of propositional variables given a logical
 * interpretation for it.
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
 * @param T - the type of indefinites to be binarized (usually String)
 */
public class IndefiniteUnarizer<T> implements IndefiniteConverter<T> {

    // Assign a PolyCircuit to each indefinite coefficient known to occur.
    private final Map<T, PolyCircuit> indefsToVars;

    // Do so also for externalIndefsToVars that have been put by the user.
    // We assume that the values the SAT solver finds for them are not
    // interesting for the user.
    private final Map<T, PolyCircuit> externalIndefsToFormulae;

    // Side constraints to ensure that unarity invariant for indefinites holds:
    // In [a_1, ..., a_n], a_i must imply a_{i-1}.
    private List<Formula<None>> prefixConditions =
        new ArrayList<Formula<None>>();

    // to be used for getting the constants ZERO and ONE and
    // new propositional variables
    private final FormulaFactory<None> formulaFactory;

    // cache the constants, they are used rather often
    private final Constant<None> ZERO;
    private final Constant<None> ONE;

    private IndefiniteUnarizer(FormulaFactory<None> formulaFactory) {
        this.indefsToVars = new LinkedHashMap<T, PolyCircuit>(128);
        this.externalIndefsToFormulae = new HashMap<T, PolyCircuit>(128);
        // feel free to change the initial sizes to better values.

        this.formulaFactory = formulaFactory;
        this.ZERO = formulaFactory.buildConstant(false);
        this.ONE = formulaFactory.buildConstant(true);
    }


    /**
     * Creates a new IndefiniteBinarizer.
     *
     * @param formulaFactory to be used for build propositional atoms
     * @return a new IndefiniteBinarizer
     */
    public static <T> IndefiniteUnarizer<T> create(FormulaFactory<None> formulaFactory) {
        return new IndefiniteUnarizer<T>(formulaFactory);
    }

    /**
     * @return the internal map from indefinite coefficients
     *  to propositional variables; <b>modify it only if you
     *  know what you are doing!</b>
     */
    @Override
    public Map<T, PolyCircuit> getIndefsToVars() {
        return this.indefsToVars;
    }

    /**
     * @param indef - indefinite for which we want to add a
     *  propositional representation.
     * @param pc - the propositional representation of indef
     */
    @Override
    public void put(T indef, PolyCircuit pc) {
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
     * @param range the range of the indefinite, at least 1
     * @return the representation of <code>indef</code> by <code>bits</code>
     *  propositional variables
     */
    public PolyCircuit bin(T indef, int range) {
        return this.bin(indef, BigInteger.valueOf(range));
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
     *
     * @param indef the indefinite to be represented in propositional logic
     * @param range the range of the indefinite, at least 1
     * @return the representation of <code>indef</code> by <code>bits</code>
     *  propositional variables
     */
    @Override
    public PolyCircuit bin(T indef, BigInteger range) {
        if (Globals.useAssertions) {
            assert (range.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0);
            assert (range.signum() > 0);
            assert (indef != null);
        }
        PolyCircuit result = this.indefsToVars.get(indef);
        if (result == null) {
            result = this.externalIndefsToFormulae.get(indef);
            if (result == null) {
                int rangeInt = range.intValue();
                List<Formula<None>> res = new ArrayList<Formula<None>>(rangeInt);
                Formula<None> oldX = null;
                for (int i = 0; i < rangeInt; ++i) {
                    Formula<None> newX = this.formulaFactory.buildVariable();
                    res.add(newX);
                    if (oldX != null) {
                        this.prefixConditions.add(this.formulaFactory.buildImplication(newX, oldX));
                    }
                    oldX = newX;
                }

                result = new PolyCircuit(res, range);
                this.indefsToVars.put(indef, result);
            }
        }
        return result;
    }

    /**
     * Create a circuit that represents the given constant.
     * @param n to be represented as a binary in propositional logic
     * @return the circuit for n.
     */
    public PolyCircuit toCircuit(final BigInteger n) {
        List<Formula<None>> formulaList = this.bin(n);
        return new PolyCircuit(formulaList, n);
    }

    /**
     * @param n to be represented as a unary in propositional logic
     * @return the unary representation of <code>n</code> in
     *  propositional logic
     */
    @Override
    public List<Formula<None>> bin(final BigInteger n) {
        if (Globals.useAssertions) {
            assert n.signum() >= 0;
            assert n.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0;
        }

        int nInt = n.intValue();
        List<Formula<None>> res = new ArrayList<Formula<None>>(nInt);
        for (int i = 0; i < nInt; ++i) {
            res.add(this.ONE);
        }
        return res;
    }

    /**
     * @param n to be represented as a unary in propositional logic
     * @return the unary representation of <code>n</code> in
     *  propositional logic
     */
    @Override
    public List<Formula<None>> bin(int n) {
        return this.bin(BigInteger.valueOf(n));
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
     * @param interpretation contains those formulae that are interpreted
     *  as true
     * @return the corresponding natural number
     */
    public int nat(List<? extends Formula<None>> formulae, Set<Integer> interpretation) {
        BigInteger resBigInt = this.natBig(formulae, interpretation);
        if (Globals.useAssertions) {
            BigInteger maxInt = BigInteger.valueOf(Integer.MAX_VALUE);
            assert resBigInt.compareTo(maxInt) <= 0;
        }
        int res = resBigInt.intValue();
        return res;
    }

    /**
     * Computes the natural number that corresponds to formulae given in the
     * interpretation. Here we use unary representation: The number k
     * is represented by the tuple
     *     [1,...,1,0,...,0]
     * where the tuple has k times the value 1 as a prefix and then continues
     * in an arbitrary number of 0s.
     *
     * @param formulae the list of formulae which are supposed to represent
     *  an indefinite coefficient.
     * @param interpretation contains those formulae that are interpreted
     *  as true
     * @return the corresponding natural number
     */
    @Override
    public BigInteger natBig(
            final List<? extends Formula<None>> formulae,
            final Set<Integer> interpretation) {
        int value = 0;
        int size = formulae.size();
        for (int i = 0; i < size; i++) {
            Formula<None> f = formulae.get(i);
            if (f.isConstant()) {
                if (f.getGateType() == CircuitGate.TRUE) {
                    ++value;
                } else { // it's a 'false'!
                    if (Globals.useAssertions) {
                        IndefiniteUnarizer.assertPrefixCondition(formulae, interpretation, i, size);
                    }
                    break;
                }
            } else if (interpretation.contains(f.getId())) {
                ++value;
            } else if (f.getId() == AbstractFormula.ID_UNSET) {
                // some formulae do not get to enter the actual CNF encoding,
                // so there is no Tseitin variable for them; get their truth
                // values in the classic style (if some actual variables of
                // theirs did not make it to the CNF either, it means that
                // their truth value does not matter overall, and we can
                // safely assume them to be 'false'
                if (f.interpret(interpretation)) {
                    ++value;
                } else { // it's a 'false'!
                    // prefix condition
                    if (Globals.useAssertions) {
                        IndefiniteUnarizer.assertPrefixCondition(formulae, interpretation, i, size);
                    }
                    break;
                }
            } else { // it's a 'false'!
                // prefix condition
                if (Globals.useAssertions) {
                    IndefiniteUnarizer.assertPrefixCondition(formulae, interpretation, i, size);
                }
                break;
            }
        }
        BigInteger result = BigInteger.valueOf(value);
        return result;
    }

    /**
     * Assertions to check that formulae entries with an index > i become false.
     * @param formulae
     * @param interpretation
     * @param i
     * @param size - size of formulae
     */
    public static void assertPrefixCondition(List<? extends Formula<None>> formulae,
        Set<Integer> interpretation, int i, int size) {
        for (int j = i+1; j < size; j++) {
            Formula<None> g = formulae.get(j);
            if (g.isConstant()) {
                assert g.getGateType() != CircuitGate.TRUE;
            }
            else {
                int id = g.getId();
                if (id == AbstractFormula.ID_UNSET) {
                    assert ! g.interpret(interpretation);
                } else {
                    assert ! interpretation.contains(id);
                }
            }
        }
    }

    /**
     * @return the encapsulated side constraints themselves - handle with care
     */
    @Override
    public List<Formula<None>> getSideConstraints() {
        return this.prefixConditions;
    }
}
