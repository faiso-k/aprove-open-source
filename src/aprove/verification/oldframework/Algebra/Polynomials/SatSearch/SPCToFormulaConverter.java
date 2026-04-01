package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts SimplePolyConstraints to a propositional formula,
 * converts models of this formula back to a mapping which
 * assigns integer values to the indefinite coefficients.
 *
 * Note: The encoding employed by this class is <b>obsolete</b>.
 * The class is kept mainly for historical reasons.
 * In doubt, use PlainSPCToCircuitConverter, which uses less "iff"s.
 *
 * Note:
 * This class was previously known as SimplePolyConstraintsToFormulaConverter
 * (-> CVS history).
 *
 * @deprecated will probably be removed in the future.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
@Deprecated
public class SPCToFormulaConverter implements PoloSatConverter {

    private final FormulaFactory<None> formulaFactory;
    private final ArithmeticFormulaFactory predefFormulaFactory;

    private final IndefiniteBinarizer<String> binarizer;

    private final Constant<None> ZERO;


    @Override
    public void setNewRanges(Map<String, BigIntegerInterval> ranges) {
       // This does not obey ranges.
    }

    @Override
    public void putRange(String a, BigInteger newRange) {
        // IGNORED.
    }

    // how many bits (propositional variables) should we use to
    // represent indefinites? Note: 2^bits - 1 == range of the search
    private final int bits;
    // TODO each indefinite should have an individual number of bits,
    //   i.e., Map<String, Integer> bits;

    private SPCToFormulaConverter(FormulaFactory<None> factory, int bits) {
        if (Globals.useAssertions) {
            assert (bits > 0);
        }
        this.formulaFactory = factory;
        this.ZERO = this.formulaFactory.buildConstant(false);
        this.predefFormulaFactory = ArithmeticFormulaFactory.create(this.formulaFactory);
        this.binarizer = IndefiniteBinarizer.create(this.formulaFactory, null);
        this.bits = AProVEMath.power(2, bits) - 1; // FIXME this.bits for range or for bits? used inconsistently!
    }

    public static SPCToFormulaConverter create(FormulaFactory<None> factory, int bits) {
        return new SPCToFormulaConverter(factory, bits);
    }

    /*
     * For understanding the convert[Aux] methods, you are referred to
     * the document in which the theory is described.
     * We use a top-down approach to the problem.
     */

    @Override
    public Pair<Formula<None>, Map<String, PolyCircuit>> convert (Set<SimplePolyConstraint> spcs,
            Set<SimplePolyConstraint> searchStrictSpcs, Abortion aborter) throws AbortionException {
        if (! searchStrictSpcs.isEmpty()) {
            throw new RuntimeException("No searchstrict with SimplePolyConstraintsToFormulaConverter so far!");
        }

        Formula<None> resultFormula;
        // the formula encodes the spcs over the range bits

        List<Formula<None>> conjuncts; // for the solution
        List<List<Formula<None>>> conjunctsLists;
        conjunctsLists = new ArrayList<List<Formula<None>>>(spcs.size());
        for (SimplePolyConstraint spc : spcs) {
            aborter.checkAbortion();
            Triple<SimplePolynomial, SimplePolynomial, ConstraintType> positivePolyConstraint;
            positivePolyConstraint = spc.toPositiveForm(true);
            conjunctsLists.add(this.convert(positivePolyConstraint.x,
                    positivePolyConstraint.y, positivePolyConstraint.z));
        }

        int conjunctsSize = 0;
        for (List<Formula<None>> list : conjunctsLists) {
            conjunctsSize += list.size();
        }
        if (Globals.useAssertions) {
            assert (conjunctsSize > 0);
        }
        if (conjunctsSize == 1) { // nothing to apply "and" on
            resultFormula = conjunctsLists.get(0).get(0);
        }
        else {
            conjuncts = new ArrayList<Formula<None>>(conjunctsSize);
            for (List<Formula<None>> list : conjunctsLists) {
                conjuncts.addAll(list);
            }
            resultFormula = this.formulaFactory.buildAnd(conjuncts);
        }
        return new Pair<Formula<None>, Map<String, PolyCircuit>>(resultFormula, this.binarizer.getIndefsToVars());
    }

    private List<Formula<None>> convert (SimplePolynomial left, SimplePolynomial right, ConstraintType constraintType) {
        // TODO clean this hack
        if (constraintType == ConstraintType.GE) {
            BigInteger rcons = right.getNumericalAddend();
            if (rcons.signum() > 0) {
                right = right.minus(SimplePolynomial.ONE);
            }
            else {
                left = left.plus(SimplePolynomial.ONE);
            }
            constraintType = ConstraintType.GT;
        }
        Pair<List<Formula<None>>, List<? extends Formula<None>>> convertLeft, convertRight;
        convertLeft = this.convert(left);
        convertRight = this.convert(right);
        List<Formula<None>> conjuncts;
        switch(constraintType) {
        case EQ: {
            List<? extends Formula<None>> eqConjuncts;
            eqConjuncts = this.predefFormulaFactory.buildEQConjuncts(convertLeft.y,
                    convertRight.y);
            conjuncts = new ArrayList<Formula<None>>(convertLeft.x.size()
                    + convertRight.x.size() + eqConjuncts.size());
            conjuncts.addAll(convertLeft.x);
            conjuncts.addAll(convertRight.x);
            conjuncts.addAll(eqConjuncts);
            return conjuncts;
        }
        case GT: {
            List<? extends Formula<None>> gtConjuncts;
            gtConjuncts = this.predefFormulaFactory.buildGTConjuncts(convertLeft.y,
                    convertRight.y);
            conjuncts = new ArrayList<Formula<None>>(convertLeft.x.size()
                    + convertRight.x.size() + gtConjuncts.size());
            conjuncts.addAll(convertLeft.x);
            conjuncts.addAll(convertRight.x);
            conjuncts.addAll(gtConjuncts);
            return conjuncts;
        }
        default: // GE, which should not happen
            throw new RuntimeException("unsuitable constraint type "
                    + constraintType +"!");
        }
    }

    private Pair<List<Formula<None>>, List<? extends Formula<None>>> convert (SimplePolynomial poly) {
        return this.convertAux(new TreeMap<IndefinitePart, BigInteger>(poly.getSimpleMonomials()));
    }

    private Pair<List<Formula<None>>, List<? extends Formula<None>>> convertAux (SortedMap<IndefinitePart, BigInteger> simpleMonomials) {

        // iterative solution this time
        int size = simpleMonomials.size();
        switch(size) {
        case 0: {
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(0);
            List<Formula<None>> outAtoms = new ArrayList<Formula<None>>(1);
            outAtoms.add(this.ZERO);
            return new Pair<List<Formula<None>>, List<? extends Formula<None>>>(conjuncts, outAtoms);
        }
        case 1: {
            Map.Entry<IndefinitePart, BigInteger> entry;
            entry = simpleMonomials.entrySet().iterator().next();
            return this.convert(entry.getKey(), entry.getValue());
        }
        case 2: {
            Iterator<Map.Entry<IndefinitePart, BigInteger>> iter;
            iter = simpleMonomials.entrySet().iterator();
            Map.Entry<IndefinitePart, BigInteger> monomial1, monomial2;
            monomial1 = iter.next();
            monomial2 = iter.next();
            List<? extends Formula<None>> conjuncts1, conjuncts2, conjuncts3;

            Pair<List<Formula<None>>, List<? extends Formula<None>>> convertM1, convertM2;
            convertM1 = this.convert(monomial1.getKey(), monomial1.getValue());
            convertM2 = this.convert(monomial2.getKey(), monomial2.getValue());

            int size1 = convertM1.y.size();
            int size2 = convertM2.y.size();
            int max12 = (size1 < size2) ? size2 : size1;
            List<? extends Formula<None>> outAtoms = this.formulaFactory.buildVariables(max12 + 1);
            conjuncts1 = this.predefFormulaFactory.buildPlusConjuncts(convertM1.y,
                    convertM2.y, outAtoms);
            conjuncts2 = convertM1.x;
            conjuncts3 = convertM2.x;
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(conjuncts1.size()
                    + conjuncts2.size() + conjuncts3.size());
            conjuncts.addAll(conjuncts1);
            conjuncts.addAll(conjuncts2);
            conjuncts.addAll(conjuncts3);
            return new Pair<List<Formula<None>>, List<? extends Formula<None>>>(conjuncts, outAtoms);
        }
        default: // sum of n > 2 addends
            List<List<? extends Formula<None>>> conjunctsLists; // List<Formula<None>>[] actually.
            final int numberOfConjunctsLists = size - 1;

            // stores the conjuncts resulting from the new plus formulae
            conjunctsLists = new ArrayList<List<? extends Formula<None>>>(numberOfConjunctsLists);

            List<Pair<List<Formula<None>>, List<? extends Formula<None>>>> convertMs;
            convertMs = new ArrayList<Pair<List<Formula<None>>, List<? extends Formula<None>>>>(size);
            for (Map.Entry<IndefinitePart, BigInteger> e : simpleMonomials.entrySet()) {
                convertMs.add(this.convert(e.getKey(), e.getValue()));
            }
            // TODO the following code is not optimal wrt space because there
            // may be ZEROes in the most significant positions of the sums,
            // which makes the formula bigger than necessary

            // build the addition formulae, using new temporary variable tuples
            // for the intermediate sums
            boolean first = true;
            Iterator<Pair<List<Formula<None>>, List<? extends Formula<None>>>> iter;
            iter = convertMs.iterator();
            List<Variable<None>> intermediateVars1 = null, intermediateVars2 = null;
            // iV1: addend, iV2: sum in the loop below

            int size1 = -1, size2, newTupleSize;
            // size_i : size of the i-th addend in the new formula
            // newTupleSize : max(size1, size2) + 1

            while (iter.hasNext()) {
                Pair<List<Formula<None>>, List<? extends Formula<None>>> currentConvert = iter.next();
                size2 = currentConvert.y.size();
                if (first) {
                    // the first two addends can be summed up immediately
                    Pair<List<Formula<None>>, List<? extends Formula<None>>> secondConvert = iter.next();
                    size1 = secondConvert.y.size();
                    newTupleSize = (size1 < size2) ? size2 + 1 : size1 + 1;
                    intermediateVars2 = this.formulaFactory.buildVariables(newTupleSize);
                    conjunctsLists.add(this.predefFormulaFactory.buildPlusConjuncts(currentConvert.y,
                            secondConvert.y, intermediateVars2));

                    // current iV2 will be an addend in the next iteration
                    intermediateVars1 = intermediateVars2;
                    size1 = newTupleSize;
                    first = false;
                }
                else {
                    // the other addends are summed up using the result of
                    // the previous iteration, i.e., intermediateVars1,
                    // and the result is stored in intermediateVars2.
                    size2 = currentConvert.y.size();
                    newTupleSize = (size1 < size2) ? size2 + 1 : size1 + 1;
                    intermediateVars2 = this.formulaFactory.buildVariables(newTupleSize);
                    conjunctsLists.add(this.predefFormulaFactory.buildPlusConjuncts(intermediateVars1,
                            currentConvert.y, intermediateVars2));

                    intermediateVars1 = intermediateVars2;
                    size1 = newTupleSize;
                }
            }

            List<? extends Formula<None>> outAtoms = intermediateVars2;
            // the value of intermediateVars2 into which we have written
            // the total sum during the final iteration

            for (Pair<List<Formula<None>>, List<? extends Formula<None>>> convertM : convertMs) {
                conjunctsLists.add(convertM.x);
            }

            // now we can compute how much space we need for conjuncts
            // so that we can avoid all those invocations of arrayCopy
            // TODO isn't that unnecessary overhead? (nah, the empirical
            // results should none of the two ways to be really better
            // than the other one, so stick to what you have got so far)
            int conjunctsSize = 0;
            for (List<? extends Formula<None>> list : conjunctsLists) {
                conjunctsSize += list.size();
            }
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(conjunctsSize);
            for (List<? extends Formula<None>> list : conjunctsLists) {
                conjuncts.addAll(list);
            }
            return new Pair<List<Formula<None>>, List<? extends Formula<None>>>(conjuncts, outAtoms);
        }
    }


    private Pair<List<Formula<None>>, List<? extends Formula<None>>> convert (IndefinitePart iPart, BigInteger factor) {
        if (Globals.useAssertions) {
            assert (factor.signum() > 0);
        }
        // just a number, the iPart is ONE
        if (iPart.isEmpty()) {
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(0);
            List<? extends Formula<None>> outAtoms = this.binarizer.bin(factor);
            return new Pair<List<Formula<None>>, List<? extends Formula<None>>>(conjuncts, outAtoms);
        }
        // if factor == 1, we can ignore it.
        if (factor.equals(BigInteger.ONE)) {
            return this.convert(iPart);
        }

        // remaining case: iPart contains at least one indefinite, and factor
        // wants some attention as well
        List<Formula<None>> conjuncts;
        List<? extends Formula<None>> conjuncts1, conjuncts2;

        Pair<List<Formula<None>>, List<? extends Formula<None>>> convertOfIPart;
        convertOfIPart = this.convert(iPart);

        List<? extends Formula<None>> binOfFactor = this.binarizer.bin(factor);
        List<? extends Formula<None>> outAtoms;
        outAtoms = this.formulaFactory.buildVariables(convertOfIPart.y.size()
                + binOfFactor.size());
        conjuncts1 = this.predefFormulaFactory.buildTimesConjuncts(convertOfIPart.y,
                binOfFactor, outAtoms);
        conjuncts2 = convertOfIPart.x;

        conjuncts = new ArrayList<Formula<None>>(conjuncts1.size()+conjuncts2.size());
        conjuncts.addAll(conjuncts1);
        conjuncts.addAll(conjuncts2);

        return new Pair<List<Formula<None>>, List<? extends Formula<None>>>(conjuncts, outAtoms);
    }

    /**
     * Converts a monomial with factor 1 (just an IndefinitePart) to a
     * List of conjuncts together with its output Atoms.
     *
     * @param iPart to be converted to a formula
     * @return
     *  x: List of conjuncts to be joined by the caller into an AndFormula,
     *     empty list means none to be joined
     *  y: List of Atoms which occur as output Atoms of x
     */
    private Pair<List<Formula<None>>, List<? extends Formula<None>>> convert (IndefinitePart iPart) {
        // Avoid the overhead of wrapping the exponents into IndefiniteParts
        // all the time because there are going to be lots of recursive calls.
        // Use a SortedMap as a wrapper to make the result (more) deterministic.
        return this.convert (new TreeMap<String, Integer>(iPart.getExponents()));
    }

    /**
     * Converts a product a_1^i_1 * ... * a_n^i_n to a pair of a list of
     * conjuncts and its output atoms.
     *
     * @param exponents mapping indefinite -> exponent, must not be null or empty
     * @return a list of conjuncts corresponding to exponents along with a list
     *  of its output atoms.
     */
    private Pair<List<Formula<None>>, List<? extends Formula<None>>> convert (SortedMap<String, Integer> exponents) {
        int size = exponents.size();
        List<Formula<None>> conjuncts; // 1st part of result
        final int conjunctsSize = 10 * size;
        // TODO better initial size, initialize only when needed size is known

        List<? extends Formula<None>> outAtoms; // 2nd part of result

        if (Globals.useAssertions) {
            // the empty IndefinitePart (ONE) should not get a formula of
            // its own, it should have been handled before this method is
            // reached
            assert(size > 0);
        }

        if (size == 1) {
            // a^power for some power > 0
            Map.Entry<String, Integer> e = exponents.entrySet().iterator().next();
            String a = e.getKey();
            int power = e.getValue();
            if (Globals.useAssertions) {
                assert(power > 0);
            }
            if (power == 1) {
                // conjuncts is empty, only the output vars matter here
                conjuncts = new ArrayList<Formula<None>>(0);
                outAtoms = this.binarizer.bin(a, this.bits).getFormulae();
            }
            else {
                conjuncts = new ArrayList<Formula<None>>(conjunctsSize);

                if (power % 2 == 0) { // power == 2*k, k > 0
                    SortedMap<String, Integer> newExponents;
                    newExponents = new TreeMap<String, Integer>();
                    newExponents.put(a, power/2);

                    Pair<List<Formula<None>>, List<? extends Formula<None>>> convertOfAToHalfPower;
                    convertOfAToHalfPower = this.convert(newExponents);

                    outAtoms = this.formulaFactory.buildVariables(2*convertOfAToHalfPower.y.size());

                    conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(convertOfAToHalfPower.y,
                            convertOfAToHalfPower.y, outAtoms));
                    conjuncts.addAll(convertOfAToHalfPower.x);
                }
                else { // power == 2*k + 1, k > 0
                    SortedMap<String, Integer> newExponents;
                    newExponents = new TreeMap<String, Integer>();
                    newExponents.put(a, power/2);

                    Pair<List<Formula<None>>, List<? extends Formula<None>>> convertOfAToHalfPower;
                    convertOfAToHalfPower = this.convert(newExponents);
                    int twoTimesNumberOfAtomsForAToHalfPower = 2 * convertOfAToHalfPower.y.size();

                    List<Variable<None>> intermediateVars;
                    intermediateVars = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower);

                    conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(convertOfAToHalfPower.y,
                            convertOfAToHalfPower.y, intermediateVars));

                    outAtoms = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower + this.bits);

                    conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(intermediateVars,
                            this.binarizer.bin(a, this.bits).getFormulae(), outAtoms));

                    conjuncts.addAll(convertOfAToHalfPower.x);
                }
            }
        }
        else {
            conjuncts = new ArrayList<Formula<None>>(conjunctsSize);
            // m * a^power for some power > 0 and some non-empty product of indefinites m
            String a = exponents.lastKey();
            int power = exponents.get(a);
            if (Globals.useAssertions) {
                assert (power > 0);
            }

            Pair<List<Formula<None>>, List<? extends Formula<None>>> convertOfM;
            convertOfM = this.convert(exponents.headMap(a));

            if (power == 1) {
                outAtoms = this.formulaFactory.buildVariables(convertOfM.y.size() + this.bits);

                conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(convertOfM.y,
                        this.binarizer.bin(a, this.bits).getFormulae(), outAtoms));
                conjuncts.addAll(convertOfM.x);
            }
            else if (power % 2 == 0) { // power == 2*k, k > 0
                SortedMap<String, Integer> newExponents;
                newExponents = new TreeMap<String, Integer>();
                newExponents.put(a, power/2);

                Pair<List<Formula<None>>, List<? extends Formula<None>>> convertOfAToHalfPower;
                convertOfAToHalfPower = this.convert(newExponents);
                int twoTimesNumberOfAtomsForAToHalfPower = 2 * convertOfAToHalfPower.y.size();

                List<Variable<None>> intermediateVars;
                intermediateVars = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower);

                conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(convertOfAToHalfPower.y,
                        convertOfAToHalfPower.y, intermediateVars));

                outAtoms = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower + convertOfM.y.size());

                conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(intermediateVars, convertOfM.y, outAtoms));
                conjuncts.addAll(convertOfAToHalfPower.x);
                conjuncts.addAll(convertOfM.x);
            }
            else { // power == 2*k + 1, k > 0
                // We here not only create the
                // conjunct for a^2k, but also the formula for a^1 in order
                // to boost efficiency (-> less method calls)
                SortedMap<String, Integer> newExponents;
                newExponents = new TreeMap<String, Integer>();
                newExponents.put(a, power/2);

                Pair<List<Formula<None>>, List<? extends Formula<None>>> convertOfAToHalfPower;
                convertOfAToHalfPower = this.convert(newExponents);
                int twoTimesNumberOfAtomsForAToHalfPower = 2 * convertOfAToHalfPower.y.size();

                List<Variable<None>> intermediateVars1, intermediateVars2;
                intermediateVars1 = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower);

                conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(convertOfAToHalfPower.y,
                        convertOfAToHalfPower.y, intermediateVars1));

                int numberOfAtomsForM = convertOfM.y.size();
                intermediateVars2 = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower+numberOfAtomsForM);

                conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(intermediateVars1,
                        convertOfM.y, intermediateVars2));

                outAtoms = this.formulaFactory.buildVariables(twoTimesNumberOfAtomsForAToHalfPower
                        + numberOfAtomsForM + this.bits);

                conjuncts.addAll(this.predefFormulaFactory.buildTimesConjuncts(intermediateVars2,
                        this.binarizer.bin(a, this.bits).getFormulae(), outAtoms));
                conjuncts.addAll(convertOfAToHalfPower.x);
                conjuncts.addAll(convertOfM.x);
            }
        }

        return new Pair<List<Formula<None>>, List<? extends Formula<None>>>(conjuncts, outAtoms);

    }

    @Override
    public FormulaFactory<None> getPropFactory() {
        return this.formulaFactory;
    }
    @Override
    public FormulaFactory<Diophantine> getDioFactory() {
        return this.formulaFactory.<Diophantine>toTheory();
    }

    @Override
    public Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(final Formula<Diophantine> f,
        final Abortion abortion) {
        throw new UnsupportedOperationException("Not implemented.");
    }

    @Override
    public Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(final Formula<Diophantine> f,
        final Collection<Formula<Diophantine>> specialSubformulae,
        final Abortion abortion) {
        throw new UnsupportedOperationException("Not implemented.");
    }

    @Override
    public Formula<None> convertDiophantine(Diophantine dio) {
        throw new UnsupportedOperationException("Not implemented.");
    }

    @Override
    public Formula<None> convertIteratively(Set<SimplePolyConstraint> spcs,
            Abortion aborter) throws AbortionException {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean getTracking() {
        return false;
    }

    @Override
    public BigInteger getRange(String a) {
        return BigInteger.valueOf(this.bits);
    }

    @Override
    public DefaultValueMap<String, BigInteger> getRanges() {
        return new DefaultValueMap<String, BigInteger>(BigInteger.valueOf(this.bits));
    }

    @Override
    public PoloSatConfigInfo getConfig() {
        // Not really applicable here, return null.
        return null;
    }

    @Override
    public IndefiniteBinarizer<String> getBinarizer() {
        return this.binarizer;
    }
}
