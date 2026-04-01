package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts sets of SimplePolyConstraints (SPCs) to Boolean circuits.
 * As opposed to propositional formulae, a fan-out > 1 is explicitly
 * desired here.
 *
 * The prefix "Plain" indicates that no fancy caching or limiting
 * stuff is taken care of here.
 *
 * Note: This case was previously known as
 * SimplePolyConstraintsToCircuitConverter. Search for this
 * name if you are interested in the corresponding CVS history.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PlainSPCToCircuitConverter extends AbstractSPCToCircuitConverter {

    private final boolean POWERS_AS_COMBS;

    // how shall we build our sums?
    private SumType sumType; /* Not final anymore since it can
                                be changed if prerequisites are not met for one type*/

    // Do we replace certain products with shifts?
    // TODO: Make it specifyable which. So far, everything is replaced.
    private final boolean useShifts;

    // If using shifts, do we use unary or binary representation?
    private final boolean binaryShifts;

    private final PoloSatConfigInfo config;



    protected PlainSPCToCircuitConverter(final FormulaFactory<None> formulaFactory,
            final Map<String, BigInteger> ranges, final BigInteger defaultRange, final PoloSatConfigInfo config) {
        super(formulaFactory, ranges, defaultRange, config);
        this.POWERS_AS_COMBS = config.getPowersAsComb();
        this.sumType = config.getSumType();
        this.useShifts = config.getUseShifts();
        this.binaryShifts = config.getBinaryShifts();
        this.config = config;
    }

    public static PlainSPCToCircuitConverter create(FormulaFactory<None> formulaFactory,
            Map<String, BigInteger> ranges, BigInteger defaultRange, PoloSatConfigInfo config) {
        return new PlainSPCToCircuitConverter(formulaFactory, ranges, defaultRange, config);
    }

    /**
     * Converts a constraint between two SimplePolynomials to a Boolean circuit
     * with just a single output node.
     *
     * @param left may only contain positive factors
     * @param right may only contain positive factors
     * @param type
     * @param returnEQ states whether the y component of the returned pair should
     *  contain the EQ constraint that corresponds to <code>left</code> and
     *  <code>right</code>.
     * @return x: the output node of the corresponding Boolean circuit
     *         y: returnEQ ? "left == right" : null
     */
    @Override
    protected Pair<Formula<None>, Formula<None>> convertConstraint(SimplePolynomial left,
            SimplePolynomial right, ConstraintType type, boolean returnEQinY) {
        Formula<None> resultX;
        Pair<Formula<None>, Formula<None>> result;
        List<Formula<None>> convertLeft, convertRight;
        convertLeft = this.convertPolynomial(left);
        convertRight = this.convertPolynomial(right);
        switch (type) {
        case EQ :
            resultX = this.formulaFactory.buildLabel(
                        this.arithmeticFactory.buildEQCircuit(convertLeft, convertRight),
                        left.toString() + type.toString() + right.toString());
            if (returnEQinY) { // in case EQ, returnEQinY is kinda pointless, but so what.
                result = new Pair<Formula<None>, Formula<None>>(resultX, resultX);
            }
            else {
                result = new Pair<Formula<None>, Formula<None>>(resultX, null);
            }
            break;
        case GT :
            resultX = this.formulaFactory.buildLabel(
                        this.arithmeticFactory.buildGTCircuit(convertLeft, convertRight),
                        left.toString() + type.toString() + right.toString());
            Formula<None> resultY = returnEQinY ? this.arithmeticFactory.buildEQCircuit(convertLeft, convertRight)
                                  : null;
            result = new Pair<Formula<None>, Formula<None>>(resultX, resultY);
            break;
        case GE :
            result = this.arithmeticFactory.buildGECircuit(convertLeft, convertRight);
            result.x = this.formulaFactory.buildLabel(
                    result.x,
                    left.toString() + type.toString() + right.toString());

            if (! returnEQinY) {
                result.y = null;
            }
            break;
        default :
            throw new RuntimeException("ConstraintType " + type +
                    " not supported for conversion to SAT and, indeed, not known so far!");
        }



        return result;
    }


    /**
     * @param polyMap to be converted to a Boolean circuit
     * @return the output nodes of the corresponding Boolean circuit
     */
    @Override
    protected PolyCircuit convertPolyMap(SortedMap<IndefinitePart, BigInteger> polyMap) {
        PolyCircuit result;
        int size = polyMap.size(); // number of monomials

        // DUAL_COMB requires two things: Unary shifts and constant parts which are split as powers of two.
        // Check the first:
        if (this.sumType == SumType.DUAL_COMB) {
            if (!this.config.getUseShifts() | this.config.getBinaryShifts()) {
                // this does not work.
                this.sumType = SumType.COMB;
                if (Globals.useAssertions) {
                    assert false;
                }
            }
        }



        switch (size) {
        case 0 : { // poly == 0
            result = new PolyCircuit(this.binarizer.bin(0), BigInteger.ZERO);
            break;
        }
        case 1 : { // poly is a monomial: n * ip, n > 0
            Map.Entry<IndefinitePart, BigInteger> entry;
            entry = polyMap.entrySet().iterator().next();
            result = this.convertMonomial(entry.getValue(), entry.getKey());
            break;
        }
        default : // our polynomial is a sum of at least 2 monomials
            // iterative solution, we may have *many* addends,
            // and we do not want any stack overflows;
            switch (this.sumType) {
            case BALANCED_UNSORTED:
            case BALANCED_SORTED: {
                // build a "balanced addition tree" instead of a comb,
                // assuming that all monomials are converted into
                // circuits with more or less the same number of
                // output nodes -> less carries needed in total
                // (# of carries of an addition of xs and ys is
                // linear in max(|xs|, |ys|) )
                List<PolyCircuit> converts;
                converts = new ArrayList<PolyCircuit>(size);
                for (Entry<IndefinitePart, BigInteger> e : polyMap.entrySet()) {
                    IndefinitePart iPart = e.getKey();
                    BigInteger factor = e.getValue();
                    PolyCircuit convertM = this.convertMonomial(factor, iPart);
                    converts.add(convertM);
                }

                // now the list converts contains at least two lists of output
                // gates -> contract it while necessary
                if (this.sumType == SumType.BALANCED_SORTED) {
                    // sort the addends via their length such that we get a
                    // really optimized solution here (at least wrt size!)

                    PolyCircuit[] convertsArray;
                    convertsArray = new PolyCircuit[0];
                    convertsArray = converts.toArray(convertsArray);
                    do {
                        Arrays.sort(convertsArray, PolyCircuit.PolyCircuitComparator.theComparator);
                        // TODO sort only if 1st time or if the prev length was odd
                        // (always sorting does not affect the result, though)

                        // if we have an odd number of addends, we put the longest
                        // addend tuple to the highest position in the list
                        boolean convertsLengthIsOdd = ((convertsArray.length & 1) == 1);
                        int newConvertsLength = convertsLengthIsOdd ? (convertsArray.length >> 1) + 1 : convertsArray.length >> 1;
                        PolyCircuit[] newConvertsArray = new PolyCircuit[newConvertsLength];
                        int iterLength = (convertsLengthIsOdd) ? convertsArray.length - 1 : convertsArray.length;
                        for (int i = 0; i < iterLength; i += 2) {
                            PolyCircuit newConvert, convI, convJ;
                            convI = convertsArray[i];
                            convJ = convertsArray[i+1];
                            newConvert = this.arithmeticFactory.buildPlusCircuit(convI, convJ);
                            newConvertsArray[i >> 1] = newConvert;
                        }
                        if (convertsLengthIsOdd) {
                            // the last element is still pending
                            newConvertsArray[newConvertsArray.length - 1] = convertsArray[convertsArray.length - 1];
                        }
                        convertsArray = newConvertsArray;
                    } while (convertsArray.length > 1);
                    result = convertsArray[0];
                }
                else { // SumType.BALANCED_UNSORTED_TREE
                    // just build the tree with the leaves from left to right
                    // the way they happen to occur in the polynomial, regardless
                    // of list length
                    do {
                        int convertsSize = converts.size();
                        boolean convertsSizeIsOdd = ((convertsSize & 1) == 1);

                        // ceil(convertsSize/2.0)
                        int currentConvertsSize = convertsSizeIsOdd ? (convertsSize >> 1) + 1 : convertsSize >> 1;

                        List<PolyCircuit> currentConverts;
                        currentConverts = new ArrayList<PolyCircuit>(currentConvertsSize);
                        int i; // list index for iteration
                        if (convertsSizeIsOdd) {
                            currentConverts.add(converts.get(0));
                            i = 1;
                        }
                        else {
                            i = 0;
                        }

                        while (i < convertsSize) {
                            PolyCircuit newConvert, convI, convJ;
                            convI = converts.get(i);
                            convJ = converts.get(i+1);
                            newConvert = this.arithmeticFactory.buildPlusCircuit(convI, convJ);
                            currentConverts.add(newConvert);
                            i += 2;
                        }
                        converts = currentConverts;
                    } while (converts.size() > 1);
                    result = converts.get(0); // converts should have exactly size 1
                }
                break;
            }
            case MINIMAL: { // just perform one addend choice at a time,
                // may yield better results e.g. for [2, 2, 10, 20]
                PolyCircuit[] convertsArray;
                convertsArray = new PolyCircuit[polyMap.size()];
                int i = 0;
                for (Entry<IndefinitePart, BigInteger> e : polyMap.entrySet()) {
                    IndefinitePart iPart = e.getKey();
                    BigInteger factor = e.getValue();
                    PolyCircuit convertM = this.convertMonomial(factor, iPart);
                    convertsArray[i] = convertM;
                    ++i;
                }

                Arrays.sort(convertsArray, PolyCircuit.PolyCircuitComparator.theComparator);
                List<PolyCircuit> converts = new LinkedList<PolyCircuit>();
                for (int j = 0; j < convertsArray.length; ++j) {
                    converts.add(convertsArray[j]);
                }

                // converts is now a list of the converted monomials;
                // it is sorted from shortest to longest one.
                do {
                    // remove the two shortest (i.e., first) elements ...
                    PolyCircuit firstOne = converts.remove(0);
                    PolyCircuit secondOne = converts.remove(0);

                    // ... build their sum ...
                    PolyCircuit sum = this.arithmeticFactory.buildPlusCircuit(firstOne, secondOne);

                    // ... and insert the sum at an appropriate place
                    ListIterator<PolyCircuit> iter;
                    iter = converts.listIterator();
                    boolean sumInserted = false;
                    while ((! sumInserted) && iter.hasNext()) {
                        PolyCircuit currentOne = iter.next();
                        if (PolyCircuit.PolyCircuitComparator.theComparator.compare(currentOne, sum) >= 0) {
                            iter.add(sum);
                            sumInserted = true;
                        }
                    }
                    if (! sumInserted) {
                        converts.add(sum);
                    }
                } while (converts.size() > 1);
                result = converts.get(0);
                break;
            }
            case COMB:  // naive construction: comb w/o any sorting
            case DUAL_COMB: // make use of dual-mixed adder
            {

                Iterator<Entry<IndefinitePart, BigInteger>> iter;
                iter = polyMap.entrySet().iterator();

                Entry<IndefinitePart, BigInteger> monomial1, monomial2;
                IndefinitePart iPart1, iPart2;
                BigInteger factor1, factor2;
                PolyCircuit convert1, convert2;

                monomial1 = iter.next();
                iPart1 = monomial1.getKey();
                factor1 = monomial1.getValue();
                convert1 = this.convertMonomial(factor1, iPart1);

                monomial2 = iter.next();
                iPart2 = monomial2.getKey();
                factor2 = monomial2.getValue();
                if (this.sumType == SumType.COMB) {

                    convert2 = this.convertMonomial(factor2, iPart2);
                    result = this.arithmeticFactory.buildPlusCircuit(convert1, convert2);

                } else /* DUAL_COMB */ {
                    result = convert1;
                    while (factor2.compareTo(BigInteger.ZERO) > 0) {
                        // Extract powers of two one by one, starting with the lowest.
                        int i = factor2.getLowestSetBit();
                        BigInteger thisPower = BigInteger.valueOf(2).pow(i);
                        factor2 = factor2.subtract(thisPower);
                        convert2 = this.convertMonomial(thisPower, iPart2);
                        result = this.arithmeticFactory.buildMixedDualAdder(result, convert2);
                    }
                }



                // all right, we have got the first two addends, but there may be
                // more, so build a tree
                while (iter.hasNext()) {
                    monomial1 = iter.next();
                    iPart1 = monomial1.getKey();
                    factor1 = monomial1.getValue();
                    if (this.sumType == SumType.COMB) {
                        convert1 = this.convertMonomial(factor1, iPart1);
                        result = this.arithmeticFactory.buildPlusCircuit(convert1, result);
                    } else /* DUAL_COMB */ {
                        while (factor1.compareTo(BigInteger.ZERO) > 0) {
                            // Extract powers of two one by one, starting with the lowest.
                            int i = factor1.getLowestSetBit();
                            BigInteger thisPower = BigInteger.valueOf(2).pow(i);
                            factor1 = factor1.subtract(thisPower);
                            convert1 = this.convertMonomial(thisPower, iPart1);
                            result = this.arithmeticFactory.buildMixedDualAdder(result, convert1);
                        }
                    }
                }
                break;
            }
            default:
                throw new RuntimeException("Unknown sum type " + this.sumType);
            }
        }
        return result;
    }

    /**
     * Converts a monomial to a Boolean circuit.
     *
     * @param factor numerical factor of the monomial, <b>must be positive!</b>
     * @param iPart the indefinites (variables) of the monomial to their
     *  corresponding powers
     * @return the output nodes of the corresponding Boolean circuit
     */
    @Override
    protected PolyCircuit convertMonomial(BigInteger factor, IndefinitePart iPart) {
        PolyCircuit result;
        if (Globals.useAssertions) {
            assert (factor.signum() > 0);
        }
        // just a number, the iPart is ONE
        if (iPart.isEmpty()) {
            result = new PolyCircuit(this.binarizer.bin(factor), factor);
        }
        // if factor == 1, we can ignore it.
        else if (factor.equals(BigInteger.ONE)) {
            result = this.convertIndefinitePart(iPart);
        }
        // the other powers of two just require shifting instead of multiplication
        else if (factor.bitCount() == 1) {
            // either 2^power (power > 0) or the negative number represented
            // by (10...0), but negative numbers are prohibited by the method
            // contract TODO check comment for BigInteger
            int power = factor.getLowestSetBit();
            PolyCircuit conv = this.convertIndefinitePart(iPart);
            List<Formula<None>> convFormulae = conv.getFormulae();
            List<Formula<None>> res = new ArrayList<Formula<None>>(convFormulae.size() + power);
            for (int i = 0; i < power; ++i) {
                res.add(this.ZERO);
            }
            res.addAll(convFormulae);
            result = new PolyCircuit(res, conv.getMax().multiply(factor));
        }
        // all right, at least two bits of factor are 1, so we are going to
        // build an actual multiplication circuit after all
        else {
            List<Formula<None>> convertFactor = this.binarizer.bin(factor);
            PolyCircuit PolyCircuitOfFactor = new PolyCircuit(convertFactor, factor);
            PolyCircuit convertIPart = this.convertIndefinitePart(iPart);
            result = this.arithmeticFactory.buildTimesCircuit(convertIPart,
                    PolyCircuitOfFactor);
        }
        return result;
    }

    /**
     * Converts a map of exponents into a PolyCircuit.
     * If we happen to use shifting where appropriate, this also checks which
     * - if any - of the indefinites in this map can be replaced by a shift.
     * The one thing to take into account if shifting is that x as a sole factor is not x but 1<<x.
     * Does not matter for a unary representation, but is important for a binary one.
     * @param exponents to be converted to a Boolean circuit
     * @return the output nodes of the corresponding Boolean circuit
     */
    @Override
    protected PolyCircuit convertExponents(SortedMap<String, Integer> exponents) {
        int size = exponents.size();
        if (Globals.useAssertions) {
            assert size > 0;
        }

        PolyCircuit result;

        if (size == 1) { // just a^n for some n
            // Straightforward if a is not shifting...
            if (!this.useShifts) {
                final Map.Entry<String, Integer> e = exponents.entrySet().iterator().next();
                final String a = e.getKey();
                final int power = e.getValue();
                result = this.convertPower(a, power);
            } else if (this.binaryShifts) {
                // Binary shifts require a bit more action than others: Not only do we need to shift, but also regard a "filter bit".
                // a^n*1 translates to 1<<(n*a). Since n should be rather small, the one multiplication here should not cause much trouble.
                // If it does, it can also be replaced by 1<<a<<a<<a...
                // Small trick: Instead of 1<<... we use a's !filterBit as 1 - if it is zero, we only need to shift Zeros and save some ands.
                final Map.Entry<String, Integer> e = exponents.entrySet().iterator().next();
                final String a = e.getKey();
                final int power = e.getValue();
                final BigInteger rangeOfA = this.getRange(a);
                final PolyCircuit aCirc = this.binarizer.bin(a, rangeOfA);

                // Bit 0 of this is a filter bit, since filtering by means of the operator is impossible here.
                if (rangeOfA.compareTo(BigInteger.ONE) > 0) {
                    if (power > 1) {
                        result = this.arithmeticFactory.buildShiftRightBinary(
                            this.arithmeticFactory.buildTimesCircuit(
                                new PolyCircuit(this.binarizer.bin(power), power), new PolyCircuit (aCirc.getFormulae().subList(1, aCirc.getFormulae().size()), aCirc.getMax())),
                                new PolyCircuit(Collections.singletonList(aCirc.getFormulae().get(0)),1));
                    } else {
                        result = this.arithmeticFactory.buildShiftRightBinary(
                            new PolyCircuit (aCirc.getFormulae().subList(1, aCirc.getFormulae().size()), aCirc.getMax()), new PolyCircuit(Collections.singletonList(aCirc.getFormulae().get(0)),1));
                    }
                } else {
                    // Binary shifting is not possible on range 1, simply use the filter.
                    // a|[0,1]^n = a
                    result = aCirc;
                }

            } else /* unary shifts */ {
                // Nice, nothing to do: for unary shifts 1<<log(x) = x. However we can only decrease the exponent by one.
                final Map.Entry<String, Integer> e = exponents.entrySet().iterator().next();
                final String a = e.getKey();
                final int power = e.getValue();
                final BigInteger rangeOfA = this.getRange(a);
                final PolyCircuit aCirc = this.binarizer.bin(a, rangeOfA);

                if (power > 1) {
                    if (this.config.getNewUnaryPower()) {
                        // We will take advantage of the fact that
                        // m << log(a) << log(a) << ... << log(a) = m << power*log(a) = m << log(a^power)
                        // and a=2^n -> a^k = 2^(power*n)
                        // Thus, if the single one in the a bit-vector is at position n, we can set it to be at position (power-1)*n in the exponented one (note that 2^0 has a one in position 0.

                        List<Formula<None>> formulae = aCirc.getFormulae();
                        List<Formula<None>> newList = new ArrayList<Formula<None>>(formulae.size() * power);
                        for (int i=0; i< formulae.size(); i++) {
                            Formula<None> f = formulae.get(i);
                            newList.add(f);
                            if (i +1 < formulae.size()) {
                                for (int j=1 /*!*/; j < power; j++) {
                                    newList.add(this.formulaFactory.buildConstant(false));
                                }
                            }
                        }
                        PolyCircuit aCircNew = new PolyCircuit(newList, aCirc.getMax().pow(power));
                        result = this.arithmeticFactory.buildShiftRightUnary(
                            aCircNew, new PolyCircuit(Collections.singletonList(((Formula<None>)this.ONE)),1));

                    } else {
                        final SortedMap<String, Integer> newMap = new TreeMap<String, Integer>(exponents);
                        newMap.put(a, power-1);
                        result = this.arithmeticFactory.buildShiftRightUnary(
                            aCirc, this.convertExponents(newMap));
                    }


                } else {
                    result = this.arithmeticFactory.buildShiftRightUnary(
                        aCirc, new PolyCircuit(Collections.singletonList(((Formula<None>)this.ONE)),1));
                }
            }
        }
        else { // m * a^power for some power > 0 and some non-empty product of indefinites m
            String a = exponents.lastKey();
            int power = exponents.get(a);
            if (Globals.useAssertions) {
                assert power > 0;
            }
            if (!this.useShifts) {
                final PolyCircuit convertOfM = this.convertExponents(exponents.headMap(a));
                final PolyCircuit convertOfAToPower = this.convertPower(a, power);

                result = this.arithmeticFactory.buildTimesCircuit(convertOfAToPower, convertOfM);
            } else if (this.binaryShifts) {
                // convert the rest...
                final PolyCircuit convertOfM = this.convertExponents(exponents.headMap(a));
                // and the individual power...
                final PolyCircuit tmpresult;
                final BigInteger rangeOfA = this.getRange(a);
                final PolyCircuit aCirc = this.binarizer.bin(a, rangeOfA);

                // Bit 0 of this is a filter bit, since filtering by means of the operator is impossible here.
                if (rangeOfA.compareTo(BigInteger.ONE) > 0) {
                    if (power > 1) {
                        tmpresult = this.arithmeticFactory.buildShiftRightBinary(
                            this.arithmeticFactory.buildTimesCircuit(
                                new PolyCircuit(this.binarizer.bin(power), power), new PolyCircuit (aCirc.getFormulae().subList(1, aCirc.getFormulae().size()), aCirc.getMax())),
                                convertOfM);
                    } else {
                        tmpresult = this.arithmeticFactory.buildShiftRightBinary(
                            new PolyCircuit (aCirc.getFormulae().subList(1, aCirc.getFormulae().size()), aCirc.getMax()), convertOfM);
                    }
                } else {
                    // Range 1 does not allow binary shifting. Use input, and filter.
                    tmpresult = convertOfM;
                }
                final List<Formula<None>> tmpres = tmpresult.getFormulae();
                // Apply filter...
                final List<Formula<None>> res = new ArrayList<Formula<None>>(tmpres.size());
                for (int i=0; i< tmpres.size(); i++) {
                    res.add(this.formulaFactory.buildAnd(aCirc.getFormulae().get(0), tmpres.get(i) ));
                }
                result = new PolyCircuit(res, tmpresult.getMax());

            } else /* unary shifts */ {

                final BigInteger rangeOfA = this.getRange(a);
                final PolyCircuit aCirc = this.binarizer.bin(a, rangeOfA);


                if (power > 1) {
                    final SortedMap<String, Integer> newMap = new TreeMap<String, Integer>(exponents);
                    if (this.config.getNewUnaryPower()) {
                        // We will take advantage of the fact that
                        // m << log(a) << log(a) << ... << log(a) = m << power*log(a) = m << log(a^power)
                        // and a=2^n -> a^k = 2^(power*n)
                        // Thus, if the single one in the a bit-vector is at position n, we can set it to be at position (power-1)*n in the exponented one (note that 2^0 has a one in position 0.
                        newMap.remove(a);
                        List<Formula<None>> formulae = aCirc.getFormulae();
                        List<Formula<None>> newList = new ArrayList<Formula<None>>(formulae.size() * power);
                        for (int i=0; i< formulae.size(); i++) {
                            Formula<None> f = formulae.get(i);
                            newList.add(f);
                            if (i +1 < formulae.size()) {
                                for (int j=1 /*!*/; j < power; j++) {
                                    newList.add(this.formulaFactory.buildConstant(false));
                                }
                            }
                        }

                        PolyCircuit aCircNew = new PolyCircuit(newList, aCirc.getMax().pow(power));
                        result = this.arithmeticFactory.buildShiftRightUnary(
                            aCircNew, this.convertExponents(newMap));

                    } else {
                        newMap.put(a, power-1);
                        result = this.arithmeticFactory.buildShiftRightUnary(
                            aCirc, this.convertExponents(newMap));
                    }
                } else {
                    final SortedMap<String, Integer> newMap = new TreeMap<String, Integer>(exponents);
                    newMap.remove(a);
                    result = this.arithmeticFactory.buildShiftRightUnary(
                        aCirc, this.convertExponents(newMap));
                }
            }
        }
        return result;
    }


    protected PolyCircuit convertPower(String a, int power) {
        if (Globals.useAssertions) {
            assert power > 0;
        }

        PolyCircuit result;
        if (power == 1) { // a^1
            BigInteger rangeOfA = this.getRange(a);
            result = this.binarizer.bin(a, rangeOfA);
        }
        else {
            if (this.POWERS_AS_COMBS) {
                // just build a comb, i.e. (...(((a*a)*a)*a)...)
                BigInteger rangeOfA = this.getRange(a);
                PolyCircuit PolyCircuitOfA = this.binarizer.bin(a, rangeOfA);
                result = PolyCircuitOfA;
                for (int i = 1; i < power; ++i) {
                    result = this.arithmeticFactory.buildTimesCircuit(result, PolyCircuitOfA);
                }
            }
            else {
                // repeated binary squaring
                if (power % 2 == 0) { // a^(2k), k > 0
                    SortedMap<String, Integer> newExponents;
                    newExponents = new TreeMap<String, Integer>();
                    newExponents.put(a, power/2);

                    PolyCircuit convertOfAToHalfPower;
                    convertOfAToHalfPower = this.convertExponents(newExponents);
                    result = this.arithmeticFactory.buildTimesCircuit(convertOfAToHalfPower,
                            convertOfAToHalfPower);
                }
                else { // a^(2k+1), k > 0
                    SortedMap<String, Integer> newExponents;
                    newExponents = new TreeMap<String, Integer>();
                    newExponents.put(a, power/2);

                    PolyCircuit convertOfAToAlmostHalfPower;
                    convertOfAToAlmostHalfPower = this.convertExponents(newExponents);
                    PolyCircuit convertOfAToPowerMinusOne;
                    convertOfAToPowerMinusOne = this.arithmeticFactory.buildTimesCircuit(convertOfAToAlmostHalfPower,
                            convertOfAToAlmostHalfPower);

                    BigInteger rangeOfA = this.getRange(a);
                    PolyCircuit PolyCircuitOfA = this.binarizer.bin(a, rangeOfA);

                    result = this.arithmeticFactory.buildTimesCircuit(convertOfAToPowerMinusOne, PolyCircuitOfA);
                }
            }
        }
        return result;
    }

    @Override
    public PoloSatConfigInfo getConfig() {
        return this.config;
    }
}
