package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.PoloSatConfigInfo.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Instances of IndefiniteBinarizer are used to convert between
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
 * @author Carsten Fuhs
 * @param <T> - the type of indefinites to be binarized (usually String)
 */
public class IndefiniteBinarizer<T> implements IndefiniteConverter<T> {

    // Maximum value for difference between desired range and the next
    // value of 2^k-1 that is at least as big as the desired range
    // for the "enumerative" approach to excluding values higher than
    // the desired range from the SAT-based search. If it is exceeded,
    // just encode "range + 1 > a".
    private static final BigInteger MAX_DIFF_FOR_EXPLICIT_EXCLUSION = BigInteger.valueOf(14L);
    private static final int MAX_DIFF_FOR_EXPLICIT_EXCLUSION_INT = 14;

    // Assign a PolyCircuit to each indefinite coefficient known to occur.
    private final Map<T, PolyCircuit> indefsToVars;

    // Do so also for externalIndefsToVars that have been put by the user.
    // We assume that the values the SAT solver finds for them are not
    // interesting for the user.
    private final Map<T, PolyCircuit> externalIndefsToFormulae;

    // to be used for getting the constants ZERO and ONE and
    // new propositional variables
    private final FormulaFactory<None> formulaFactory;

    // to be used for the GT circuit for range side constraints
    // in case of big ranges != 2^k - 1
    private final ArithmeticFactory arithmeticFactory;

    // stores the side constraints that arise for ranges != 2^k - 1
    private final List<Formula<None>> sideConstraints;

    // cache the constants, they are used rather often
    private final Constant<None> ZERO;
    private final Constant<None> ONE;

    // ConfigInfo. Can be null - then default is used. Used fields are the ones for shifting.
    private final PoloSatConfigInfo config;

    private IndefiniteBinarizer(final FormulaFactory<None> formulaFactory, final PoloSatConfigInfo config) {
        this.indefsToVars = new LinkedHashMap<T, PolyCircuit>(128);
        this.externalIndefsToFormulae = new HashMap<T, PolyCircuit>(128);
        // feel free to change the initial sizes to better values.

        this.formulaFactory = formulaFactory;
        this.ZERO = formulaFactory.buildConstant(false);
        this.ONE = formulaFactory.buildConstant(true);
        this.sideConstraints = new ArrayList<Formula<None>>();
        this.config = config;
        this.arithmeticFactory =
            ArithmeticCircuitFactory.create(this.formulaFactory, this.config == null ? new PoloSatConfigInfo()
                : this.config);
    }

    /**
     * Creates a new IndefiniteBinarizer.
     *
     * @param formulaFactory to be used for build propositional atoms
     * @return a new IndefiniteBinarizer
     */
    public static <T> IndefiniteBinarizer<T> create(final FormulaFactory<None> formulaFactory) {
        return new IndefiniteBinarizer<T>(formulaFactory, null);
    }

    /**
     * Creates a new IndefiniteBinarizer, possibly with options for shifting.
     *
     * @param formulaFactory to be used for build propositional atoms
     * @param config may be null, then defaults are used
     * @return a new IndefiniteBinarizer
     */
    public static <T> IndefiniteBinarizer<T> create(final FormulaFactory<None> formulaFactory,
        final PoloSatConfigInfo config) {
        return new IndefiniteBinarizer<T>(formulaFactory, config);
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
    public void put(final T indef, final PolyCircuit pc) {
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
    public PolyCircuit bin(final T indef, final int range) {
        if (this.config != null && this.config.getUseShifts()) {
            // Some special logic needed; since this method is not used often, we use this method.
            return this.bin(indef, BigInteger.valueOf(range));
        }
        if (Globals.useAssertions) {
            assert (range > 0);
            assert (indef != null);
        }
        PolyCircuit result = this.indefsToVars.get(indef);
        if (result == null) {
            result = this.externalIndefsToFormulae.get(indef);
            if (result == null) {
                final int bits = AProVEMath.binaryLength(range);
                List<Formula<None>> resultX;
                resultX = new ArrayList<Formula<None>>(bits);
                for (int i = 0; i < bits; ++i) {
                    resultX.add(this.formulaFactory.buildVariable());
                }

                result = new PolyCircuit(resultX, range);
                this.indefsToVars.put(indef, result);
            }
        }
        return result;
    }

    /**
     * Returns the corresponding representation of an indefinite coefficient
     * of a polynomial which consists of as many propositional variables as
     * bits are needed for range. For a given indefinite, the result will
     * always be the same (it will be cached once it has been computed), so the
     * range passed to bin should be constant for a given value of indef.
     *
     * Necessary side constraints for the range are taken care of
     * automatically, but you must explicitly get them from this
     * IndefiniteBinarizer in the end.
     *
     * @param indef the indefinite to be represented in propositional logic
     * @param range the range of the indefinite, at least 1
     * @return the representation of <code>indef</code> by <code>bits</code>
     *  propositional variables
     */
    @Override
    public PolyCircuit bin(final T indef, final BigInteger range) {
        if (Globals.useAssertions) {
            assert (range.signum() > 0);
            assert (indef != null);
        }
        PolyCircuit result = this.indefsToVars.get(indef);
        if (result == null) {
            result = this.externalIndefsToFormulae.get(indef);
            if (result == null) {

                List<Formula<None>> resultX;

                // In unary mode, we also need to take care that the unary condition is fulfilled.
                if (this.config == null || !this.config.getUseShifts() || this.config.getBinaryShifts()) {

                    int bits;

                    // In binary mode, we need one bit more than the range's log. Furthermore assert that the range is a power of 2.
                    if (this.config != null && this.config.getUseShifts() && this.config.getBinaryShifts()) {
                        if (Globals.useAssertions) {
                            assert range.bitCount() == 1;
                        }
                        // log(log(...))
                        bits = AProVEMath.binaryLength(range.bitLength() - 1) + 1;

                    } else {
                        bits = range.bitLength();
                    }

                    resultX = new ArrayList<Formula<None>>(bits);
                    for (int i = 0; i < bits; ++i) {
                        final Variable<None> freshVar = this.formulaFactory.buildVariable();
                        freshVar.setDescription(indef.toString() + "[" + bits + "]_" + i);
                        resultX.add(freshVar);
                    }
                } else {

                    // Unary mode; Note that 000000 is also valid! (So condition is: 1 or less 1s in the binary representation
                    // Represented as circuit in the following way:
                    // (alternative representations thinkable)
                    // b0: x0; b1: x1 & !x0; b2: x2 & !x1 & !x0; ...
                    final int bits = range.bitLength();

                    final List<Formula<None>> nots = new ArrayList<Formula<None>>(bits);
                    resultX = new ArrayList<Formula<None>>(bits);
                    for (int i = 0; i < bits; i++) {
                        // Get a fresh variable...
                        final Variable<None> freshVar = this.formulaFactory.buildVariable();
                        freshVar.setDescription(indef.toString() + "[2<<" + bits + "]_2<<" + i);
                        final Formula<None> fv = freshVar;

                        if (this.config.getUnaryMode() != UNARY_MODE.CIRCUIT || i == 0) { //unary condition currently encoded in different method */
                            // Just the variable
                            resultX.add(fv);
                        } else {
                            // The capsule is necessary: Later on we are interested in the truth value of the whole formula. It thus cannot be optimized away.
                            resultX.add(this.formulaFactory.buildCapsule(this.formulaFactory.buildAnd(fv,
                                this.formulaFactory.buildAnd(nots))));
                        }
                        nots.add(this.formulaFactory.buildNot(fv));
                    }
                }

                result = new PolyCircuit(resultX, range);
                this.indefsToVars.put(indef, result);
                final List<Formula<None>> rangeConstraints = this.excludeUpperBits(range, resultX);
                this.sideConstraints.addAll(rangeConstraints);
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
        final List<Formula<None>> formulaList = this.bin(n);
        return new PolyCircuit(formulaList, n);
    }

    /**
     * @param n to be represented as a binary in propositional logic
     * @return the binary representation of <code>n</code> in
     *  propositional logic
     */
    @Override
    public List<Formula<None>> bin(final BigInteger n) {
        if (Globals.useAssertions) {
            assert (n.signum() >= 0);
        }

        if (n.signum() == 0) {
            final List<Formula<None>> result = new ArrayList<Formula<None>>(1);
            result.add(this.ZERO);
            return result;
        }

        // length = ceil(log_2(n+1));
        final int length = n.bitLength(); //32 - Integer.numberOfLeadingZeros(n);
        final List<Formula<None>> result = new ArrayList<Formula<None>>(length);

        for (int i = 0; i < length; ++i) {
            final boolean ithBitIsSet = n.testBit(i);
            result.add(ithBitIsSet ? this.ONE : this.ZERO);
        }

        if (Globals.useAssertions) {
            assert (result.get(length - 1) != this.ZERO);
        }

        return result;
    }

    /**
     * @param n to be represented as a binary in propositional logic
     * @return the binary representation of <code>n</code> in
     *  propositional logic
     */
    @Override
    public List<Formula<None>> bin(final int n) {
        if (Globals.useAssertions) {
            assert (n >= 0);
        }

        if (n == 0) {
            final List<Formula<None>> result = new ArrayList<Formula<None>>(1);
            result.add(this.ZERO);
            return result;
        }

        // length = ceil(log_2(n+1));
        final int length = 32 - Integer.numberOfLeadingZeros(n);
        final List<Formula<None>> result = new ArrayList<Formula<None>>(length);

        int mask = 1; // masks exactly one bit of n
        for (int i = 0; i < length; ++i) {
            if ((n & mask) != 0) {
                result.add(this.ONE);
            } else {
                result.add(this.ZERO);
            }
            mask <<= 1; // mask the next bit
        }

        if (Globals.useAssertions) {
            assert (result.get(length - 1) != this.ZERO);
        }

        return result;
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
    public int nat(final List<? extends Formula<None>> formulae, final Set<Integer> interpretation) {
        if (this.config == null || !this.config.getUseShifts() || !this.config.getBinaryShifts()) {

            if (Globals.useAssertions) {
                assert (formulae.size() <= 31);
            }

            int result = 0;
            int twoToTheN = 1;
            for (final Formula<None> f : formulae) {
                if (f.isConstant()) {
                    // constants don't care about interpretations
                    final int gateType = f.getGateType();
                    if (gateType == CircuitGate.TRUE) {
                        result += twoToTheN;
                    }
                } else if (interpretation.contains(f.getId())) {
                    // variables or non-atomic formulae do in general, though
                    result += twoToTheN;
                } else if (f.getId() == AbstractFormula.ID_UNSET) {
                    // some formulae do not get to enter the actual CNF encoding,
                    // so there is no Tseitin variable for them; get their truth
                    // values in the classic style (if some actual variables of
                    // theirs did not make it to the CNF either, it means that
                    // their truth value does not matter overall, and we can
                    // safely assume them to be 'false'
                    if (f.interpret(interpretation)) {
                        result += twoToTheN;
                    }
                }
                twoToTheN <<= 1; // twoToTheN *= 2;
            }
            return result;

        } else /* binary shifts */{
            // The lowest-order bit is the filter bit.
            final Formula<None> filter = formulae.get(0);
            if (filter.isConstant()) {
                // constants don't care about interpretations
                final int gateType = filter.getGateType();
                if (gateType == CircuitGate.FALSE) {
                    return 0;
                }
            } else if (!interpretation.contains(filter.getId())) {
                return 0;
            }

            final List<? extends Formula<None>> mFormulae = formulae.subList(1, formulae.size());
            int tmpRes = 0;
            int twoToTheN = 1;
            for (final Formula<None> f : mFormulae) {
                if (f.isConstant()) {
                    // constants don't care about interpretations
                    final int gateType = f.getGateType();
                    if (gateType == CircuitGate.TRUE) {
                        tmpRes += twoToTheN;
                    }
                } else if (interpretation.contains(f.getId())) {
                    // variables or non-atomic formulae do in general, though
                    tmpRes += twoToTheN;
                } else if (f.getId() == AbstractFormula.ID_UNSET) {
                    // some formulae do not get to enter the actual CNF encoding,
                    // so there is no Tseitin variable for them; get their truth
                    // values in the classic style (if some actual variables of
                    // theirs did not make it to the CNF either, it means that
                    // their truth value does not matter overall, and we can
                    // safely assume them to be 'false'
                    if (f.interpret(interpretation)) {
                        tmpRes += twoToTheN;
                    }
                }
                twoToTheN <<= 1; // twoToTheN *= 2;
            }
            final int result = AProVEMath.power(2, tmpRes);
            return result;
        }

    }

    /**
     * Computes the natural number that corresponds to formulae given in the
     * interpretation. I.e.:
     *  sum over all indices i of atoms
     *    2^i*interpretation(formulae.get(i))
     *  (true == 1, false == 0),
     *  constants are interpreted the natural way
     *
     * @param formulae the list of formulae which are supposed to represent
     *  an indefinite coefficient.
     * @param interpretation contains those formulae that are interpreted
     *  as true
     * @return the corresponding natural number
     */
    @Override
    public BigInteger natBig(final List<? extends Formula<None>> formulae, final Set<Integer> interpretation) {

        BigInteger result = BigInteger.ZERO;
        BigInteger twoToTheN = BigInteger.ONE;

        if (this.config == null || !this.config.getUseShifts() || !this.config.getBinaryShifts()) {
            for (final Formula<None> f : formulae) {
                if (f.isConstant()) {
                    // constants don't care about interpretations
                    final int gateType = f.getGateType();
                    if (gateType == CircuitGate.TRUE) {
                        result = result.add(twoToTheN);
                    }
                } else if (interpretation.contains(f.getId())) {
                    // variables or non-atomic formulae do in general, though
                    result = result.add(twoToTheN);
                } else if (f.getId() == AbstractFormula.ID_UNSET) {
                    // some formulae do not get to enter the actual CNF encoding,
                    // so there is no Tseitin variable for them; get their truth
                    // values in the classic style (if some actual variables of
                    // theirs did not make it to the CNF either, it means that
                    // their truth value does not matter overall, and we can
                    // safely assume them to be 'false'
                    if (f.interpret(interpretation)) {
                        result = result.add(twoToTheN);
                    }
                }
                twoToTheN = twoToTheN.shiftLeft(1); // twoToTheN *= 2;
            }
            return result;

        } else /* binary shifts */{
            // The lowest-order bit is the filter bit.
            final Formula<None> filter = formulae.get(0);
            BigInteger tmpRes = BigInteger.ZERO;
            if (filter.isConstant()) {
                // constants don't care about interpretations
                final int gateType = filter.getGateType();
                if (gateType == CircuitGate.FALSE) {
                    return BigInteger.ZERO;
                }
            } else if (!interpretation.contains(filter.getId())) {
                return BigInteger.ZERO;
            }

            final List<? extends Formula<None>> mFormulae = formulae.subList(1, formulae.size());
            for (final Formula<None> f : mFormulae) {
                if (f.isConstant()) {
                    // constants don't care about interpretations
                    final int gateType = f.getGateType();
                    if (gateType == CircuitGate.TRUE) {
                        tmpRes = tmpRes.add(twoToTheN);
                    }
                } else if (interpretation.contains(f.getId())) {
                    // variables or non-atomic formulae do in general, though
                    tmpRes = tmpRes.add(twoToTheN);
                } else if (f.getId() == AbstractFormula.ID_UNSET) {
                    // some formulae do not get to enter the actual CNF encoding,
                    // so there is no Tseitin variable for them; get their truth
                    // values in the classic style (if some actual variables of
                    // theirs did not make it to the CNF either, it means that
                    // their truth value does not matter overall, and we can
                    // safely assume them to be 'false'
                    if (f.interpret(interpretation)) {
                        tmpRes = tmpRes.add(twoToTheN);
                    }
                }
                twoToTheN = twoToTheN.shiftLeft(1); // twoToTheN *= 2;
            }
            if (tmpRes.bitLength() > 32 & Globals.useAssertions) {
                assert false; // We cannot display such high numbers.
            }
            result = BigInteger.ONE.shiftLeft(tmpRes.intValue());
            return result;
        }

    }

    /**
     * Creates additional conjuncts to add to the result formula ensuring only valid combinations can be used.
     * Determines the correct form using the range for a given variable and the POLOSAT configuration.
     *
     * @note kabasci: Moved from AbstractSPCToCircuitConverter, as needs more functionality with shifts. WAS:
     * Helper method for allowing arbitrary natural ranges for
     * Diophantine variables, not only 2^k - 1. Generates clauses
     * that prohibit values greater than range.
     *
     * @param range - maximum range allowed for vars;
     *  may be at most 2^vars.size() - 1
     * @param variables - tuple of variables (formulae) that is supposed
     *  to represent some Diophantine variable
     *  @param arithmeticFactory - The arithmetic factory to be used for creating constraints of sorts.
     * @return conjuncts for enforcing that I(vars) <= range for
     *  any model I of the circuit in construction
     */
    private List<Formula<None>> excludeUpperBits(final BigInteger range, final List<Formula<None>> vars) {
        final int bits = vars.size();

        final List<Formula<None>> result = new ArrayList<Formula<None>>(0);

        // Which type of variable do we have?
        // Simple: Prevent too large numbers.
        if (this.config == null || !this.config.getUseShifts()) {

            if (Globals.useAssertions) {
                assert bits >= range.bitLength();
            }

            final BigInteger max = BigInteger.valueOf(2L).pow(bits).subtract(BigInteger.ONE);

            if (range.equals(max)) {
                return Collections.<Formula<None>>emptyList();
            }

            final BigInteger diff = max.subtract(range);
            if (diff.compareTo(IndefiniteBinarizer.MAX_DIFF_FOR_EXPLICIT_EXCLUSION) > 0) {
                // if the difference between the desired range and the maximal
                // possible value for the given number of bits exceeds a certain
                // value, we just encode "range > a+1" where "a" is the
                // Diophantine variable whose encoding supposedly is vars.
                final BigInteger rangePlusOne = range.add(BigInteger.ONE);
                final List<Formula<None>> binarizedRangePlusOne = this.bin(rangePlusOne);
                final Formula<None> resultFormula = this.arithmeticFactory.buildGTCircuit(binarizedRangePlusOne, vars);
                result.add(resultFormula);
                return result;
            } else {
                // specify each prohibited combination of values for the bits
                // in vars individually as conjuncts

                final List<Formula<None>> notVars = new ArrayList<Formula<None>>(bits);
                for (int i = 0; i < bits; ++i) {
                    notVars.add(this.formulaFactory.buildNot(vars.get(i)));
                }

                /*
                if (false) {
                    if (range == 5 && bits == 3) {
                        // exclude 6 and 7:
                        // one of the two most significant bits must be false
                        Formula<None> f1, f2, notBoth;
                        f1 = this.formulaFactory.buildNot(vars.get(1));
                        f2 = this.formulaFactory.buildNot(vars.get(2));
                        notBoth = this.formulaFactory.buildOr(f1, f2);
                        List<Formula<None>> result = new ArrayList<Formula<None>>(1);
                        result.add(notBoth);
                        return result;
                    }
                }
                */

                for (BigInteger i = range.add(BigInteger.ONE); i.compareTo(max) <= 0; i = i.add(BigInteger.ONE)) {
                    final List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(bits);
                    for (int j = 0; j < bits; ++j) {
                        if (i.testBit(j)) {
                            disjuncts.add(notVars.get(j));
                        } else {
                            disjuncts.add(vars.get(j));
                        }
                    }
                    result.add(this.formulaFactory.buildOr(disjuncts));
                }

                return result;
            }

        } else if (this.config.getUseShifts() & !this.config.getBinaryShifts()) {
            // Unary shifts: Depending on mode, encode sideconstraints for unary condition.

            if (this.config.getUnaryMode() == UNARY_MODE.SIDECONSTRAINTS) {
                final SATPatterns<None> pat = new SATPatterns<None>(this.formulaFactory);

                result.add(pat.encodeAtMostOne(vars));
            }

            return result;

        } else /*if (config.getUseShifts() & config.getBinaryShifts())*/{

            // Binary shifts; prohibit the following:
            // first, the filter bit implies that all other bits be zero (for efficiency)

            if (vars.size() < 2) {
                // Nothing to be done.
                return result;
            }

            final List<Formula<None>> notVars = new ArrayList<Formula<None>>(bits);
            for (int i = 0; i < bits; ++i) {
                notVars.add(this.formulaFactory.buildNot(vars.get(i)));
            }

            for (int i = 1; i < vars.size(); i++) {
                result.add(this.formulaFactory.buildImplication(notVars.get(0), notVars.get(i)));
            }

            // Second, limit the range accordingly.
            // We assume the range is correctly dimensioned (i.e. power of two). First calc the real range...
            final int lv = range.bitLength() - 1;

            final int max = AProVEMath.power(2, bits - 1) - 1;

            if (range.equals(BigInteger.valueOf(max))) {
                return Collections.<Formula<None>>emptyList();
            }

            final int diff = max - lv;
            if (diff > IndefiniteBinarizer.MAX_DIFF_FOR_EXPLICIT_EXCLUSION_INT) {
                // if the difference between the desired range and the maximal
                // possible value for the given number of bits exceeds a certain
                // value, we just encode "range > a+1" where "a" is the
                // Diophantine variable whose encoding supposedly is vars.

                final List<Formula<None>> binarizedRangePlusOne = this.bin(lv + 1);
                final Formula<None> resultFormula =
                    this.arithmeticFactory.buildGTCircuit(binarizedRangePlusOne, vars.subList(1, bits));
                result.add(resultFormula);
                return result;
            } else {
                // specify each prohibited combination of values for the bits
                // in vars individually as conjuncts

                for (int i = lv + 1; i <= max; i++) {
                    final List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(bits);
                    for (int j = 0; j < (bits - 1); ++j) {
                        if ((i & AProVEMath.power(2, j)) != 0) {
                            disjuncts.add(notVars.get(j + 1));
                        } else {
                            disjuncts.add(vars.get(j + 1));
                        }
                    }
                    result.add(this.formulaFactory.buildOr(disjuncts));
                }

            }

            return result;
        }
    }

    @Override
    public List<Formula<None>> getSideConstraints() {
        return this.sideConstraints;
    }
}
