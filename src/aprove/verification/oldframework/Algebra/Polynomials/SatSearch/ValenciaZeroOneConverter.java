package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * SAT encoding for Diophantine constraints over {0, 1}
 * (i.e., non-linear Pseudo-Boolean constraints) as
 * described in the PROLE'07 paper by Lucas and Navarro
 * from Valencia.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class ValenciaZeroOneConverter implements PoloSatConverter {

    private final FormulaFactory<None> formulaFactory;

    private final IndefiniteBinarizer<String> binarizer;

    private boolean neqSearchstrict;
    private boolean gtAsSuch;

    private ValenciaZeroOneConverter(FormulaFactory<None> formulaFactory,
            boolean neqSearchstrict, boolean gtAsSuch) {
        this.formulaFactory = formulaFactory;
        this.binarizer = IndefiniteBinarizer.create(this.formulaFactory, null);
        this.neqSearchstrict = neqSearchstrict;
        this.gtAsSuch = gtAsSuch;
    }

    /**
     *
     * @param formulaFactory
     * @param neqSearchstrict - use \lnot \bigwedge p = 0 instead of
     *  \bigvee p > 0 for searchstrict constraints
     * @param gtAsSuch - if (! neqSearchstrict):
     *  encode p > 0 as such and not as p - 1 >= 0 for searchstrict
     *  constraints
     * @return
     */
    public static ValenciaZeroOneConverter create(FormulaFactory<None> formulaFactory,
            boolean neqSearchstrict, boolean gtAsSuch) {
        return new ValenciaZeroOneConverter(formulaFactory, neqSearchstrict,
                gtAsSuch);
    }

    @Override
    public Pair<Formula<None>, Map<String, PolyCircuit>> convert(
            Set<SimplePolyConstraint> spcs,
            Set<SimplePolyConstraint> searchStrictSpcs,
            Abortion aborter) throws AbortionException {
        int conjunctsSize = searchStrictSpcs.isEmpty() ? spcs.size() : spcs.size() + searchStrictSpcs.size() + 1;
        List<Formula<None>> conjuncts; // will be the args of result
        conjuncts = new ArrayList<Formula<None>>(conjunctsSize);

        for (SimplePolyConstraint spc : spcs) {
            aborter.checkAbortion();
            Formula<None> converted = this.convertConstraint(spc);
            conjuncts.add(converted);
        }

        if (! searchStrictSpcs.isEmpty()) {
            if (this.neqSearchstrict) {
                // ... proceed like in the case of "normal" constraints, but
                // remember each of the corresponding EQ-constraints
                List<Formula<None>> searchStrictEqs = new ArrayList<Formula<None>>(searchStrictSpcs.size());
                for (SimplePolyConstraint spc : searchStrictSpcs) {
                    aborter.checkAbortion();
                    // all as GE
                    Formula<None> converted = this.convertConstraint(spc);
                    conjuncts.add(converted);

                    // keep corresponding EQ encoding as well
                    SimplePolyConstraint eqSPC = new SimplePolyConstraint(spc.getPolynomial(), ConstraintType.EQ);
                    Formula<None> eqConverted = this.convertConstraint(eqSPC);
                    searchStrictEqs.add(eqConverted);
                }

                // now state that not all of these EQ-constraints may hold
                Formula<None> allSearchStrictEQ = this.formulaFactory.buildAnd(searchStrictEqs);
                Formula<None> strictnessEnforcingConjunct = this.formulaFactory.buildNot(allSearchStrictEQ);
                conjuncts.add(strictnessEnforcingConjunct);
            }
            else {
                List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(searchStrictSpcs.size());
                for (SimplePolyConstraint spc : searchStrictSpcs) {
                    aborter.checkAbortion();
                    // all as GE
                    Formula<None> converted = this.convertConstraint(spc);
                    conjuncts.add(converted);

                    // and (at least) one as GT
                    Formula<None> gtConverted;
                    if (this.gtAsSuch) {
                        SimplePolynomial sp = spc.getPolynomial();
                        gtConverted = this.convertPolyWithAddend(ConstraintType.GT,
                                sp, BigInteger.ZERO);
                    }
                    else {
                        SimplePolyConstraint strictSpc = new SimplePolyConstraint(spc.getPolynomial(),
                                ConstraintType.GT);
                        gtConverted = this.convertConstraint(strictSpc);
                    }
                    disjuncts.add(gtConverted);
                }
                conjuncts.add(this.formulaFactory.buildOr(disjuncts));
            }
        }
        Formula<None> result = this.formulaFactory.buildAnd(conjuncts);
        Map<String, PolyCircuit> indefsToVars = this.binarizer.getIndefsToVars();
        return new Pair<Formula<None>, Map<String, PolyCircuit>>(result, indefsToVars);
    }

    /**
     * Converts spc to propositional logic (with range 0-1).
     *
     * @param spc
     * @return
     */
    private Formula<None> convertConstraint(SimplePolyConstraint spc) {
        ConstraintType rel = spc.getType();
        SimplePolynomial poly = spc.getPolynomial();
        Formula<None> result = this.convertPolyWithAddend(rel, poly, BigInteger.ZERO);
        return result;
    }

    /**
     * Converts poly + addend  rel  0.
     *
     * @param rel
     * @param poly
     * @param addend
     * @return
     */
    private Formula<None> convertPolyWithAddend(ConstraintType rel,
            SimplePolynomial poly, BigInteger addend) {
        ImmutableMap<IndefinitePart, BigInteger> monomials = poly.getSimpleMonomials();
        return this.convertWithAddend(rel, monomials, addend);
    }

    private Formula<None> convertWithAddend(ConstraintType rel,
            Map<IndefinitePart, BigInteger> monomials, BigInteger addend) {
        if (monomials.isEmpty()) {
            // end of recursion
            switch (rel) {
            case GE:
                return this.formulaFactory.buildConstant(addend.signum() >= 0);
            case EQ:
                return this.formulaFactory.buildConstant(addend.signum() == 0);
            case GT:
                return this.formulaFactory.buildConstant(addend.signum() > 0);
            default:
                throw new RuntimeException("Unknown ConstraintType " + rel + "!");
            }
        }
        else {
            Iterator<Entry<IndefinitePart, BigInteger>> iter = monomials.entrySet().iterator();
            Entry<IndefinitePart, BigInteger> firstMonomial = iter.next();
            Set<String> firstIndefinites = firstMonomial.getKey().getExponents().keySet();

            if (firstIndefinites.isEmpty()) {
                // found the constant addend, it will be used in the last step
                BigInteger newAddend = addend.add(firstMonomial.getValue());

                // build remaining poly
                Map<IndefinitePart, BigInteger> rmMMap = new LinkedHashMap<IndefinitePart, BigInteger>(monomials.size() - 1);
                while (iter.hasNext()) {
                    Entry<IndefinitePart, BigInteger> monomial = iter.next();
                    rmMMap.put(monomial.getKey(), monomial.getValue());
                }
                return this.convertWithAddend(rel, rmMMap, newAddend);
            }
            else {
                // Compute the polynomials that result when the product of
                // firstIndefinites becomes 0 or 1, respectively
                // (i.e., rmM and rmV).
                Map<IndefinitePart, BigInteger> rmMMap = new LinkedHashMap<IndefinitePart, BigInteger>(monomials.size() - 1);
                Map<IndefinitePart, BigInteger> rmVMap = new LinkedHashMap<IndefinitePart, BigInteger>(monomials.size() - 1);
                {
                    while (iter.hasNext()) {
                        Entry<IndefinitePart, BigInteger> monomial = iter.next();
                        IndefinitePart oldFactors = monomial.getKey();
                        if (! oldFactors.containsAll(firstIndefinites)) {
                            // if product of firstIndefinites becomes 0, then
                            // also any monomial that contains all of
                            // firstIndefinites.
                            rmMMap.put(oldFactors, monomial.getValue());
                        }

                        // no need to represent factors of which we know
                        // that they take value 1.
                        IndefinitePart newFactors = oldFactors.removeIndefinites(firstIndefinites);
                        BigInteger monomCoeff = monomial.getValue();

                        // the resulting smaller monomial might already be present.
                        BigInteger coeff = rmVMap.get(newFactors);
                        if (coeff == null) {
                            rmVMap.put(newFactors, monomCoeff);
                        }
                        else {
                            BigInteger diff = coeff.add(monomCoeff);
                            if (diff.signum() == 0) {
                                rmVMap.remove(newFactors);
                            }
                            else {
                                rmVMap.put(newFactors, diff);
                            }
                        }
                    }
                }

                // Two cases:
                // (a) one of the indefinites of the current monomial
                //     becomes zero.
                List<Formula<None>> varsForIndefs = new ArrayList<Formula<None>>(firstIndefinites.size());
                List<Formula<None>> notIndefsArgs = new ArrayList<Formula<None>>(firstIndefinites.size());
                for (String indef : firstIndefinites) {
                    Formula<None> var = this.getVarForIndef(indef);
                    varsForIndefs.add(var);
                    notIndefsArgs.add(this.formulaFactory.buildNot(var));
                }
                Formula<None> someIndefZero = this.formulaFactory.buildOr(notIndefsArgs);
                Formula<None> rmMFormula = this.convertWithAddend(rel, rmMMap, addend);
                Formula<None> resArg1 = this.formulaFactory.buildAnd(someIndefZero, rmMFormula);

                // (b) or all of them take value one.
                Formula<None> allIndefsOne = this.formulaFactory.buildAnd(varsForIndefs);

                //    remember the numerical coeff of the first monomial
                //    as additional addend
                BigInteger newAddend = addend.add(firstMonomial.getValue());
                Formula<None> rmVWithNewAddendFormula = this.convertWithAddend(rel, rmVMap, newAddend);
                Formula<None> resArg2 = this.formulaFactory.buildAnd(allIndefsOne, rmVWithNewAddendFormula);
                return this.formulaFactory.buildOr(resArg1, resArg2);
            }
        }
    }

    /**
     * Here Diophantine variables correspond to just a single formula.
     *
     * @param indef
     * @return
     */
    private Formula<None> getVarForIndef(final String indef) {
         return this.binarizer.bin(indef, 1).getFormulae().get(0);
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

    /**
     * The method makes no sense here, since
     * range 1 is all that is supported here.
     */
    @Override
    public void setNewRanges(Map<String, BigIntegerInterval> newRanges) {
        throw new UnsupportedOperationException("Range fixed to 1 for Valencian encoding!");
    }

    @Override
    public Formula<None> convertDiophantine(Diophantine dio) {
        SimplePolynomial poly = dio.getLeft().minus(dio.getRight());
        SimplePolyConstraint spc = new SimplePolyConstraint(poly, dio.getRelation());
        return this.convertConstraint(spc);
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
    public boolean getTracking() {
        return false;
    }

    @Override
    public BigInteger getRange(String a) {
        return BigInteger.ONE;
    }

    @Override
    public DefaultValueMap<String, BigInteger> getRanges() {
        return new DefaultValueMap<String, BigInteger>(BigInteger.ONE);
    }

    @Override
    public void putRange(String a, BigInteger newRange) {
        // Only range 1 is supported, so requests for special treatment
        // for "a" are kinda pointless and are IGNORED.
    }

    @Override
    public PoloSatConfigInfo getConfig() {
        // Not applicable, return null
        return null;
    }

    /**
     * TODO test this method
     */
    @Override
    public Formula<None> convertIteratively(Set<SimplePolyConstraint> spcs,
            Abortion aborter) throws AbortionException {
        return this.convert(spcs, Collections.<SimplePolyConstraint>emptySet(),
                aborter).x;
    }

    @Override
    public IndefiniteBinarizer<String> getBinarizer() {
        return this.binarizer;
    }
}
