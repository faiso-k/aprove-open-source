package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Common abstract superclass for several variants of the conversion of
 * SimplePolyConstraints to Circuits.
 *
 * Note: Much of the code of this class was contained in the
 * (removed) class SimplePolyConstraintToCircuitConverter
 * (-> CVS history).
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractSPCToCircuitConverter implements PoloSatConverter {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.AbstractSPCToCircuitConverter");


    protected final FormulaFactory<None> formulaFactory;

    protected ArithmeticFactory arithmeticFactory;

    protected final IndefiniteConverter<String> binarizer;

    protected final BigInteger defaultRange; // range for those a_i \notin ranges.keySet()

    // should not be final; iterative solution requires this.
    protected Map<String, BigInteger> ranges;

    protected final GTMode gtMode;

    protected final boolean productAbstraction;

    protected final boolean neqSearchstrict;

    protected final Constant<None> ZERO;
    protected final Constant<None> ONE;

    private final boolean TRACKING;
    // for informational purposes only

    @Override
    public void setNewRanges(Map<String, BigIntegerInterval> ranges) {
        Map<String, BigInteger> newMap = new LinkedHashMap<String, BigInteger>(ranges.size());
        for (Map.Entry<String, BigIntegerInterval> entry: ranges.entrySet()) {
            newMap.put(entry.getKey(), entry.getValue().max);
        }

        this.ranges = newMap;
    }

    protected AbstractSPCToCircuitConverter(FormulaFactory<None> formulaFactory,
            Map<String, BigInteger> ranges, BigInteger defaultRange,
            PoloSatConfigInfo config) {
        if (Globals.useAssertions) {
            assert defaultRange.signum() > 0 :
                "Non-positive default range: " + defaultRange;
            for (BigInteger n : ranges.values()) {
                assert n.signum() > 0 :
                    "Additional ranges contain non-positive value: " + ranges;
            }
        }
        this.formulaFactory = formulaFactory;
        if (config.getUnaryIndefinites()) {
            this.arithmeticFactory =
                ArithmeticUnaryCircuitFactory.create(this.formulaFactory, config);
            this.binarizer =
                IndefiniteUnarizer.<String>create(this.formulaFactory);
        } else {
            this.arithmeticFactory =
                ArithmeticCircuitFactory.create(this.formulaFactory, config);
            this.binarizer =
                IndefiniteBinarizer.<String>create(this.formulaFactory, config);
        }

        this.defaultRange = defaultRange;
        this.ranges = ranges;
        /*
        this.defaultBits = AProVEMath.binaryLength(defaultRange);
        this.bits = new HashMap<String, Integer>(ranges.size());
        for (Map.Entry<String, Integer> e : ranges.entrySet()) {
            int range = e.getValue();
            int length = AProVEMath.binaryLength(range);
            this.bits.put(e.getKey(), length);
        }
        */
        this.ZERO = this.formulaFactory.buildConstant(false);
        this.ONE = this.formulaFactory.buildConstant(true);
        this.gtMode = config.getGtMode();
        this.productAbstraction = config.getProductAbstraction();
        this.TRACKING = config.getTracking();
        this.neqSearchstrict = config.getNeqSearchstrict();
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
    protected abstract Pair<Formula<None>, Formula<None>> convertConstraint(SimplePolynomial left,
            SimplePolynomial right, ConstraintType type, boolean returnEQinY);

    /**
     * @param polyMap to be converted to a Boolean circuit
     * @return the output nodes of the corresponding Boolean circuit
     */
    protected abstract PolyCircuit convertPolyMap(SortedMap<IndefinitePart, BigInteger> polyMap);

    /**
     * Converts a monomial to a Boolean circuit.
     *
     * @param factor numerical factor of the monomial, <b>must be positive!</b>
     * @param iPart the indefinites (variables) of the monomial to their
     *  corresponding powers
     * @return the output nodes of the corresponding Boolean circuit
     */
    protected abstract PolyCircuit convertMonomial(BigInteger factor, IndefinitePart iPart);

    /**
     * @param exponents to be converted to a Boolean circuit
     * @return the output nodes of the corresponding Boolean circuit
     */
    protected abstract PolyCircuit convertExponents(SortedMap<String, Integer> exponents);


    @Override
    public Formula<None> convertDiophantine(Diophantine dio) {
        SimplePolynomial lhs = dio.getLeft();
        SimplePolynomial rhs = dio.getRight();
        ConstraintType type = dio.getRelation();
        return this.convertConstraint(lhs, rhs, type, false).x;
    }

    /**
     * Converts a Diophantine formula to a triple of a purely propositional
     * formula, a mapping from indefinites to the corresponding lists
     * of formulae and a mapping from the occurring prop. variables in f to
     * the corresponding prop. variables of x
     *
     * @param f - to be converted
     * @return
     *  x - a corresponding purely propositional formula<br>
     *  y - the mapping indefinite -> [formula] which can be used for the
     *      correspondence of Diophantine and propositional problem.<br>
     *  z - map from the occurring prop. variables in f to the corresponding
     *      prop. variables of x
     */
    @Override
    public Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(final Formula<Diophantine> f,
        final Abortion abortion) throws AbortionException {
        final Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>,
            Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> protoRes =
            this.convert(f, Collections.<Formula<Diophantine>> emptySet(), abortion);

        Triple<Formula<None>, Map<String, PolyCircuit> , Map<Variable<Diophantine>, Variable<None>>> result =
            new Triple<Formula<None>, Map<String, PolyCircuit> , Map<Variable<Diophantine>, Variable<None>>>(
                protoRes.x, protoRes.y, protoRes.z);
        return result;
    }

    @Override
    public Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(final Formula<Diophantine> f,
        final Collection<Formula<Diophantine>> specialSubformulae,
        final Abortion abortion) throws AbortionException {
        final DiophantineToSATVisitor v = DiophantineToSATVisitor.create(this);
        abortion.checkAbortion();
        Formula<None> propFormula = f.apply(v);
        abortion.checkAbortion();

        // now make sure that no values outside the allowed ranges are found
        Map<String, PolyCircuit> indefsToVars = this.binarizer.getIndefsToVars();
        List<Formula<None>> newConjuncts;
        newConjuncts = new ArrayList<Formula<None>>(2*indefsToVars.size());
        newConjuncts.addAll(this.binarizer.getSideConstraints());
        Formula<None> res = this.formulaFactory.buildLabel(
                                this.formulaFactory.buildAnd(newConjuncts), "Indefinite binarizer side constraints for range requirements");
        newConjuncts = new ArrayList<Formula<None>>(2);
        newConjuncts.add(res);
        newConjuncts.add(propFormula);
        propFormula = this.formulaFactory.buildAnd(newConjuncts);

        Map<Formula<Diophantine>, Formula<None>> specialSubformulaeToNone =
            new LinkedHashMap<Formula<Diophantine>, Formula<None>>(specialSubformulae.size());
        for (Formula<Diophantine> dioFml : specialSubformulae) {
            Formula<None> propFml = v.get(dioFml);
            if (Globals.useAssertions) {
                assert propFml != null;
            }
            specialSubformulaeToNone.put(dioFml, propFml);
        }

        Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>,
            Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> result =
                new Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>,
                    Map<String, PolyCircuit> , Map<Variable<Diophantine>, Variable<None>>>(
                            specialSubformulaeToNone, propFormula, indefsToVars, v.getVarMapping());
        return result;
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
    public Pair<Formula<None>, Map<String, PolyCircuit>> convert(Set<SimplePolyConstraint> spcsSet,
            Set<SimplePolyConstraint> searchStrictSpcsSet, Abortion aborter) throws AbortionException {

        aborter.checkAbortion();

        List<SimplePolyConstraint> spcs, searchStrictSpcs;
        if (this.productAbstraction) {
            long nanos1 = System.nanoTime();
            spcs = new ArrayList<SimplePolyConstraint>(spcsSet);
            searchStrictSpcs = new ArrayList<SimplePolyConstraint>(searchStrictSpcsSet);
            aborter.checkAbortion();
            this.abstractProducts(spcs, searchStrictSpcs);
            long nanos2 = System.nanoTime();

            if (AbstractSPCToCircuitConverter.log.isLoggable(Level.FINEST)) {
                AbstractSPCToCircuitConverter.log.log(Level.FINEST,
                        "Product abstraction incl. times circuit construction took {0} ns and yielded:\nNormal constraints:\n",
                        nanos2 - nanos1);
                for (SimplePolyConstraint spc : spcs) {
                    AbstractSPCToCircuitConverter.log.finest(spc + "\n");
                }
                AbstractSPCToCircuitConverter.log.finest("Searchstrict constraints:\n");
                for (SimplePolyConstraint spc : searchStrictSpcs) {
                    AbstractSPCToCircuitConverter.log.finest(spc + "\n");
                }
            }
        }
        else {
            spcs = new ArrayList<SimplePolyConstraint>(spcsSet);
            searchStrictSpcs = new ArrayList<SimplePolyConstraint>(searchStrictSpcsSet);
        }

        Formula<None> resultX;
        int conjunctsSize = searchStrictSpcs.isEmpty() ? spcs.size() : spcs.size() + searchStrictSpcs.size() + 1;
        List<Formula<None>> conjuncts; // will be the args of result
        conjuncts = new ArrayList<Formula<None>>(conjunctsSize);

        // just reduce to converting the lhs and rhs polynomials
        // (-> no negative numbers) and to expressing the relation
        // between them
        for (SimplePolyConstraint spc : spcs) {
            aborter.checkAbortion();
            Triple<SimplePolynomial, SimplePolynomial, ConstraintType> positivePolyConstraint;
            positivePolyConstraint = spc.toPositiveForm(true);
            Pair<Formula<None>, Formula<None>> converted = this.convertConstraint(positivePolyConstraint.x,
                    positivePolyConstraint.y, positivePolyConstraint.z, false);
            conjuncts.add(converted.x);
        }

        // if there are searchstrict constraints to be handled ...
        if (! searchStrictSpcs.isEmpty()) {
            if (this.neqSearchstrict) {
                // ... proceed like in the case of "normal" constraints, but
                // remember each of the corresponding EQ-constraints
                List<Formula<None>> searchStrictEqs = new ArrayList<Formula<None>>(searchStrictSpcs.size());
                for (SimplePolyConstraint spc : searchStrictSpcs) {
                    aborter.checkAbortion();
                    Triple<SimplePolynomial, SimplePolynomial, ConstraintType> positivePolyConstraint;
                    positivePolyConstraint = spc.toPositiveForm(false);
                    Pair<Formula<None>, Formula<None>> converted = this.convertConstraint(positivePolyConstraint.x,
                            positivePolyConstraint.y, positivePolyConstraint.z, true);
                    conjuncts.add(converted.x);
                    searchStrictEqs.add(converted.y);
                }

                // now state that not all of these EQ-constraints may hold
                Formula<None> allSearchStrictEQ = this.formulaFactory.buildAnd(searchStrictEqs);
                Formula<None> strictnessEnforcingConjunct = this.formulaFactory.buildNot(allSearchStrictEQ);
                conjuncts.add(strictnessEnforcingConjunct);
            }
            else {
                List<Formula<None>> searchStrictGts = new ArrayList<Formula<None>>(searchStrictSpcs.size());
                for (SimplePolyConstraint spc : searchStrictSpcs) {
                    aborter.checkAbortion();
                    Triple<SimplePolynomial, SimplePolynomial, ConstraintType> positivePolyConstraint;
                    positivePolyConstraint = spc.toPositiveForm(false);
                    Pair<Formula<None>, Formula<None>> convertedGTEQ = this.convertConstraint(positivePolyConstraint.x,
                            positivePolyConstraint.y, ConstraintType.GT, true);
                    Formula<None> convertedGE = this.formulaFactory.buildOr(convertedGTEQ.x, convertedGTEQ.y);
                    conjuncts.add(convertedGE);
                    searchStrictGts.add(convertedGTEQ.x);
                }
                Formula<None> someStrict = this.formulaFactory.buildOr(searchStrictGts);
                conjuncts.add(someStrict);
            }
        }

        Map<String, PolyCircuit> indefsToVars = this.binarizer.getIndefsToVars();

        // BEGIN UGLY HACK FOR RANGE 0, 1, 4, 5 (generally, numbers with their
        // 2nd bit being 0 in binary representation)
        /*
        if (false) {
            if (this.defaultBits > 2) {
                List<Formula<None>> newConjuncts;
                newConjuncts = new ArrayList<Formula<None>>(indefsToVars.size() + conjuncts.size());
                for (List<Formula<None>> vars : indefsToVars.values()) {
                    Formula<None> negateSecondBit = this.formulaFactory.buildNot(vars.get(1));
                    newConjuncts.add(negateSecondBit);
                }
                newConjuncts.addAll(conjuncts);
                resultX = this.formulaFactory.buildAnd(newConjuncts);
            }
        }
        */
        // END UGLY HACK

        // now make sure that no values outside the allowed ranges are found
        List<Formula<None>> newConjuncts;
        newConjuncts = new ArrayList<Formula<None>>(2*indefsToVars.size() + conjuncts.size());
        newConjuncts.add(this.formulaFactory.buildLabel(this.formulaFactory.buildAnd(this.binarizer.getSideConstraints()), "Indefinite binarizer side constraints for range requirements"));
        newConjuncts.addAll(conjuncts);
        resultX = this.formulaFactory.buildAnd(newConjuncts);

        if (Globals.DEBUG_FUHS) {
            if (false) {
                if (this.formulaFactory instanceof FullSharingFlatteningFactory) {
                    FullSharingFlatteningFactory fsff = (FullSharingFlatteningFactory) this.formulaFactory;
                    System.out.println("Constraints == " + spcs);
                    System.out.println("    FullSharingFlatteningFactory reports:");
                    System.out.println("    NotFormula cache hits: " + fsff.notHits);
                    System.out.println("    NotFormula cache misses: " + fsff.notMisses);
                    System.out.println("    AndFormula cache hits: " + fsff.andHits);
                    System.out.println("    AndFormula cache misses: " + fsff.andMisses);
                    System.out.println("    OrFormula cache hits: " + fsff.orHits);
                    System.out.println("    OrFormula cache misses: " + fsff.orMisses);
                    System.out.println("    XorFormula cache hits: " + fsff.xorHits);
                    System.out.println("    XorFormula cache misses: " + fsff.xorMisses);
                    System.out.println("    IffFormula cache hits: " + fsff.iffHits);
                    System.out.println("    IffFormula cache misses: " + fsff.iffMisses);
                }
            }
        }
        aborter.checkAbortion();
        return new Pair<Formula<None>, Map<String, PolyCircuit>>(resultX, indefsToVars);
    }

    /**
     * @param poly to be converted to a Boolean circuit
     * @return the output nodes of the corresponding Boolean circuit
     */
    protected List<Formula<None>> convertPolynomial(SimplePolynomial poly) {
        SortedMap<IndefinitePart, BigInteger> polyMap;
        polyMap = new TreeMap<IndefinitePart, BigInteger>(poly.getSimpleMonomials());
        return this.convertPolyMap(polyMap).getFormulae();
    }

    /**
     * @param iPart to be converted to a Boolean circuit
     * @return the output nodes of the corresponding Boolean circuit
     */
    protected PolyCircuit convertIndefinitePart(IndefinitePart iPart) {
        SortedMap<String, Integer> exponents;
        exponents = new TreeMap<String, Integer>(iPart.getExponents());
        return this.convertExponents(exponents);
    }

    @Override
    public Formula<None> convertIteratively(Set<SimplePolyConstraint> spcsSet,
            Abortion aborter) throws AbortionException {
        List<SimplePolyConstraint> spcs;
        if (this.productAbstraction) {
            long nanos1 = System.nanoTime();
            spcs = new ArrayList<SimplePolyConstraint>(spcsSet);
            aborter.checkAbortion();
            this.abstractProducts(spcs, java.util.Collections.<SimplePolyConstraint>emptyList());
            long nanos2 = System.nanoTime();

            if (AbstractSPCToCircuitConverter.log.isLoggable(Level.FINEST)) {
                AbstractSPCToCircuitConverter.log.log(Level.FINEST,
                        "Product abstraction incl. times circuit construction took {0} ns and yielded:\n",
                        nanos2 - nanos1);
                for (SimplePolyConstraint spc : spcs) {
                    AbstractSPCToCircuitConverter.log.finest(spc + "\n");
                }
            }
        }
        else {
            spcs = new ArrayList<SimplePolyConstraint>(spcsSet);
        }

        int conjunctsSize = spcs.size();
        List<Formula<None>> conjuncts; // will be the args of result
        conjuncts = new ArrayList<Formula<None>>(conjunctsSize);

        // just reduce to converting the lhs and rhs polynomials
        // (-> no negative numbers) and to expressing the relation
        // between them
        for (SimplePolyConstraint spc : spcs) {
            aborter.checkAbortion();
            Triple<SimplePolynomial, SimplePolynomial, ConstraintType> positivePolyConstraint;
            positivePolyConstraint = spc.toPositiveForm(true);
            Pair<Formula<None>, Formula<None>> converted = this.convertConstraint(positivePolyConstraint.x,
                    positivePolyConstraint.y, positivePolyConstraint.z, false);
            conjuncts.add(converted.x);
        }
        Formula<None> result = this.formulaFactory.buildAnd(conjuncts);
        return result;
    }

    @Override
    public BigInteger getRange(String a) {
        BigInteger result = this.ranges.get(a);
        return result == null ? this.defaultRange : result;
    }

    @Override
    public DefaultValueMap<String, BigInteger> getRanges() {
        DefaultValueMap<String, BigInteger> result = new DefaultValueMap<String, BigInteger>(this.defaultRange);
        result.putAll(this.ranges);
        return result;
    }

    @Override
    public void putRange(String a, BigInteger newRange) {
        this.ranges.put(a, newRange);
    }



    /**
     * Performs product abstraction for the elements of spcs and moreSpcs.
     *
     * @param spcs
     * @param moreSpcs
     */
    private void abstractProducts(List<SimplePolyConstraint> spcs, List<SimplePolyConstraint> moreSpcs) {
        Set<String> forbiddenIndefs = new HashSet<String>();
        for (SimplePolyConstraint spc : spcs) {
            forbiddenIndefs.addAll(spc.getIndefinites());
        }
        for (SimplePolyConstraint spc : moreSpcs) {
            forbiddenIndefs.addAll(spc.getIndefinites());
        }

        ProductAbstractor abstractor = new ProductAbstractor(forbiddenIndefs);
        LinkedHashMap<String, StringPair> abstractedProducts;
        abstractedProducts = abstractor.abstractProducts(spcs, moreSpcs, this.ranges, this.defaultRange);

        // Now build the concrete products, our binarizer will remember them!
        // Note the order of the entries in abstractedProducts:
        //   If we tried to build the propositional representation of c*d
        //   if we had not already built propositional representations of
        //   c and d, things would get messy.
        for (Entry<String, StringPair> e : abstractedProducts.entrySet()) {
            String abstractedIndef = e.getKey();
            StringPair factors = e.getValue();
            PolyCircuit pc1, pc2, product;
            pc1 = this.binarizer.bin(factors.one, this.getRange(factors.one));
            pc2 = this.binarizer.bin(factors.two, this.getRange(factors.two));
            product = this.arithmeticFactory.buildTimesCircuit(pc1, pc2);
            this.binarizer.put(abstractedIndef, product);
        }
    }


    @Override
    public boolean getTracking() {
        return this.TRACKING;
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
    public IndefiniteConverter<String> getBinarizer() {
        return this.binarizer;
    }
}
